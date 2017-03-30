module GAT
export @signature, @instance, BaseExpr, head, args

using Base.Meta: show_sexpr
using AutoHashEquals
import DataStructures: OrderedDict
using Match

# Data types
############

abstract BaseExpr{T}

constructor{T}(::Type{BaseExpr{T}}) = T
head{T}(::BaseExpr{T}) = T
args(expr::BaseExpr) = expr.args

# Internal data types
#####################

@auto_hash_equals immutable JuliaFunction
  call_expr::Expr
  return_type::Nullable{Union{Symbol,Expr}}
  impl::Nullable{Expr}
  
  function JuliaFunction(call_expr, return_type=Nullable(), impl=Nullable()) 
    new(call_expr, return_type, impl)
  end
end

@auto_hash_equals immutable JuliaFunctionSig
  name::Symbol
  types::Vector{Union{Symbol,Expr}}
end

typealias Context OrderedDict{Symbol,Union{Symbol,Expr}}

@auto_hash_equals immutable TypeConstructor
  name::Symbol
  params::Vector{Symbol}
  context::Context
end

@auto_hash_equals immutable TermConstructor
  name::Symbol
  params::Vector{Symbol}
  typ::Union{Symbol,Expr}
  context::Context
end

@auto_hash_equals immutable SignatureBinding
  name::Symbol
  params::Vector{Symbol}
end

""" Signature for a generalized algebraic theory (GAT).
"""
@auto_hash_equals immutable Signature
  types::OrderedDict{Symbol,TypeConstructor}
  terms::OrderedDict{Symbol,TermConstructor}
end

""" Class = GAT signature + Julia-specific content.
"""
immutable Class
  name::Symbol
  params::Vector{Symbol}
  signature::Signature
  functions::Vector{JuliaFunction}
end

# Julia expressions
###################

""" Parse Julia function definition into standardized form.
"""
function parse_function(expr::Expr)::JuliaFunction
  fun_expr, impl = @match expr begin
    Expr(:(=), args, _) => args
    Expr(:function, args, _) => args
    _ => throw(ParseError("Ill-formed function definition $(as_sexpr(expr))"))
  end
  @match fun_expr begin
    (Expr(:(::), [Expr(:call, args, _), return_type], _) => 
      JuliaFunction(Expr(:call, args...), return_type, impl))
    (Expr(:call, args, _) =>
      JuliaFunction(Expr(:call, args...), Nullable(), impl))
    _ => throw(ParseError("Ill-formed function header $(as_sexpr(fun_expr))"))
  end
end

""" Parse signature of Julia function.
"""
function parse_function_sig(call_expr::Expr)::JuliaFunctionSig
  name, args = @match call_expr begin
    Expr(:call, [name::Symbol, args...], _) => (name, args)
    _ => throw(ParseError("Ill-formed function signature $(as_sexpr(call_expr))"))
  end
  types = [ @match expr begin
      Expr(:(::), [_, typ::Symbol], _) => typ
      Expr(:(::), [typ::Symbol], _) => typ
      _ => :Any
    end for expr in args ]
  JuliaFunctionSig(name, types)
end
parse_function_sig(fun::JuliaFunction) = parse_function_sig(fun.call_expr)

""" Generate Julia expression for function definition.
"""
function gen_function(fun::JuliaFunction)::Expr
  if isnull(fun.return_type)
    head = fun.call_expr
  else 
    head = Expr(:(::), fun.call_expr, get(fun.return_type))
  end
  if isnull(fun.impl)
    body = Expr(:block)
  else
    # Wrap implementation inside block if not already.
    impl = get(fun.impl)
    body = impl.head == :block ? impl : Expr(:block, impl)
  end
  Expr(:function, head, body)
end

""" Convert Julia expression to S-expression.
"""
function as_sexpr(expr)::AbstractString
  io = IOBuffer()
  show_sexpr(io, expr)
  takebuf_string(io)
end

""" Remove all :line annotations from a Julia expression.
"""
function filter_line(expr::Expr; recurse::Bool=false)::Expr
  args = filter(x -> !(isa(x, Expr) && x.head == :line), expr.args)
  if recurse
    args = [ isa(x, Expr) ? filter_line(x; recurse=true) : x for x in args ]
  end
  Expr(expr.head, args...)
end
  
# GAT expressions
#################

""" Parse a raw expression in a GAT.

A "raw expression" is a just composition of function and constant symbols.
"""
function parse_raw_expr(expr)
  @match expr begin
    Expr(:call, args, _) => map(parse_raw_expr, args)
    head::Symbol => nothing
    _ => throw(ParseError("Ill-formed raw expression $(as_sexpr(expr))"))
  end
  expr # Return the expression unmodified. This function just checks syntax.
end

""" Parse context for term or type in a GAT.
"""
function parse_context(expr::Expr)::Context
  @assert expr.head == :tuple
  context = OrderedDict()
  for arg in expr.args
    name, typ = @match arg begin
      Expr(:(::), [name::Symbol, typ], _) => (name, parse_raw_expr(typ))
      _ => throw(ParseError("Ill-formed context expression $(as_sexpr(expr))"))
    end
    push_unique!(context, name, typ)
  end
  return context
end

""" Parse type or term constructor in a GAT.
"""
function parse_constructor(expr::Expr)::Union{TypeConstructor,TermConstructor}
  # Context is optional.
  cons_expr, context = @match expr begin
    Expr(:call, [:<=, inner, context], _) => (inner, parse_context(context))
    _ => (expr, Context())
  end
  
  # Allow abbreviated syntax where tail of context is included in parameters.
  function parse_params(params)::Vector{Symbol}
    [ @match param begin
        Expr(:(::), [name::Symbol, typ], _) => begin
          push_unique!(context, name, parse_raw_expr(typ))
          name
        end
        name::Symbol => name
        _ => throw(ParseError("Ill-formed type/term parameter $(as_sexpr(param))"))
      end for param in params ]
  end
  
  @match cons_expr begin
    (Expr(:(::), [name::Symbol, :TYPE], _)
      => TypeConstructor(name, [], context))
    (Expr(:(::), [Expr(:call, [name::Symbol, params...], _), :TYPE], _)
      => TypeConstructor(name, parse_params(params), context))
    (Expr(:(::), [Expr(:call, [name::Symbol, params...], _), typ], _)
      => TermConstructor(name, parse_params(params), parse_raw_expr(typ), context))
    _ => throw(ParseError("Ill-formed type/term constructor $(as_sexpr(cons_expr))"))
  end
end

""" Generate abstract type definition from a GAT type constructor.
"""
function gen_abstract_type(cons::TypeConstructor)::Expr
  Expr(:abstract, Expr(:(<:), 
    Expr(:curly, esc(cons.name), esc(:T)),
    Expr(:curly, :BaseExpr, esc(:T))))
end

# Signatures
############

""" TOOD
"""
macro signature(head, body)
  # Parse signature: GAT and extra Julia functions.
  head = parse_signature_binding(head)
  types, terms, functions = parse_signature_body(body)
  signature = Signature(types, terms)
  class = Class(head.name, head.params, signature, functions)
  
  # Generate module: signature definition and method stubs.
  all_functions = [ interface(signature); functions ]
  body = Expr(:block, [
    esc(Expr(:export, [cons.name for cons in values(types)]...));
    esc(Expr(:export, unique(f.call_expr.args[1] for f in all_functions)...));
  
    [ gen_abstract_type(cons) for cons in values(types) ];
    [ esc(gen_function(fun)) for fun in all_functions ];
    
    esc(:(class() = $(class)));
  ]...)
  # Modules must be at top level:
  # https://github.com/JuliaLang/julia/issues/21009
  mod = Expr(:module, true, esc(head.name), body)
  return Expr(:toplevel, mod)
end

function parse_signature_binding(expr::Expr)::SignatureBinding
  @match expr begin
    Expr(:call, [name::Symbol, params...], _) => SignatureBinding(name, params)
    _ => throw(ParseError("Ill-formed signature binding $(as_sexpr(expr))"))
  end
end

""" Parse the body of a GAT signature declaration.
"""
function parse_signature_body(expr::Expr)
  @assert expr.head == :block
  types, terms, funs = OrderedDict(), OrderedDict(), []
  for elem in filter_line(expr).args
    if elem.head in (:(::), :call)
      cons = parse_constructor(elem)
      @match cons begin
        cons::TypeConstructor => push_unique!(types, cons.name, cons)
        cons::TermConstructor => push_unique!(terms, cons.name, cons)
      end
    elseif elem.head in (:(=), :function)
      push!(funs, parse_function(elem))
    else
      throw(ParseError("Ill-formed signature element $(as_sexpr(elem))"))
    end
  end
  return (types, terms, funs)
end

""" Julia functions for type parameter accessors.
"""
function accessors(sig::Signature)::Vector{JuliaFunction}
  vcat(map(accessors, values(sig.types))...)
end
function accessors(cons::TypeConstructor)::Vector{JuliaFunction}
  [ JuliaFunction(Expr(:call, p, Expr(:(::), cons.name)),
                  strip_type(cons.context[p]))
    for p in cons.params ]
end

""" Julia functions for term constructors of GAT.
"""
function constructors(sig::Signature)::Vector{JuliaFunction}
  map(constructor, values(sig.terms))
end
function constructor(cons::TermConstructor)::JuliaFunction
  return_type = strip_type(cons.typ)
  if isempty(cons.params)
    # Special case: term constructors with no arguments dispatch on term type.
    args = [ :(::Type{$return_type}) ]
  else
    args = [ Expr(:(::), p, strip_type(cons.context[p])) for p in cons.params ]
  end
  call_expr = Expr(:call, cons.name, args...)
  JuliaFunction(call_expr, return_type)
end

function interface(sig::Signature)::Vector{JuliaFunction}
  [ accessors(sig); constructors(sig) ]
end
function interface(class::Class)::Vector{JuliaFunction}
  [ interface(class.signature); class.functions ]
end

# Instances
###########

""" TODO
"""
macro instance(head, body)
  # Parse the instance definition.
  head = parse_signature_binding(head)
  functions = parse_instance_body(body)
  
  # We must generate and evaluate the code at *run time* because the signature
  # module is not defined at *parse time*.  
  expr = :(instance_code($(esc(head.name)), $(esc(head.params)), $functions))
  Expr(:call, esc(:eval), expr)
end
function instance_code(mod, instance_types, instance_fns)
  # Explicitly import the stub definitions.
  # FIXME: Is this necessary?
  class = mod.class()
  class_fns = interface(class)
  imports = [ Expr(:import, class.name, name)
              for name in unique(f.call_expr.args[1] for f in class_fns) ]
  code = Expr(:block, imports...)
  
  # Method definitions.
  bindings = Dict(zip(class.params, instance_types))
  bound_fns = [ replace_types(bindings, f) for f in class_fns ]
  bound_fns = OrderedDict(parse_function_sig(f) => f for f in bound_fns)
  instance_fns = Dict(parse_function_sig(f) => f for f in instance_fns)
  for (sig, f) in bound_fns
    if haskey(instance_fns, sig)
      f_impl = instance_fns[sig]
    elseif !isnull(f.impl)
      f_impl = f
    else
      error("Method $(f.call_expr) not implemented in $(class.name) instance")
    end
    push!(code.args, gen_function(f_impl))
  end
  return code
end

""" Parse the body of a GAT instance definition.
"""
function parse_instance_body(expr::Expr)::Vector{JuliaFunction}
  @match filter_line(expr) begin
    Expr(:block, args, _) => map(parse_function, args)
    _ => throw(ParseEror("Ill-formed instance definition"))
  end  
end

# Utility functions
###################

""" Push key-value pair unless there is a key collision.
"""
function push_unique!(collection, key, value)
  if haskey(collection, key)
    throw(ParseError("Name $key already defined"))
  end
  collection[key] = value
end

""" Recursively replace types in Julia expression.
"""
function replace_types(bindings::Dict, f::JuliaFunction)::JuliaFunction
  JuliaFunction(
    replace_types(bindings, f.call_expr),
    isnull(f.return_type) ? Nullable() : replace_type(bindings, get(f.return_type)),
    f.impl)
end
function replace_types(bindings::Dict, expr::Union{Symbol,Expr})
  recurse(expr) = replace_types(bindings, expr)
  @match expr begin
    (Expr(:(::), [fst, snd::Symbol], _) => 
      Expr(:(::), [recurse(fst), replace_type(bindings, snd)]...))
    Expr(head, args, _) => Expr(head, map(recurse, args)...)
    _ => expr
  end
end
function replace_type(bindings::Dict, typ::Symbol)
  get(bindings, typ, typ)
end

""" Remove type parameters from dependent type.
"""
function strip_type(expr)::Symbol
  @match expr begin
    Expr(:call, [head::Symbol, args...], _) => head
    sym::Symbol => sym
  end
end

end
