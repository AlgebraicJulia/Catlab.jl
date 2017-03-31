module GAT
export @signature, @instance

using AutoHashEquals
import DataStructures: OrderedDict
using Match

# Data types
############

""" Base type for method stubs in GAT signature.
"""
abstract Stub

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

""" Signature for a generalized algebraic theory (GAT).
"""
@auto_hash_equals immutable Signature
  types::Vector{TypeConstructor}
  terms::Vector{TermConstructor}
end

immutable SignatureBinding
  name::Symbol
  params::Vector{Symbol}
end

immutable SignatureHead
  main::SignatureBinding
  base::Vector{SignatureBinding}
  SignatureHead(main, base=[]) = new(main, base)
end

""" Typeclass = GAT signature + Julia-specific content.
"""
immutable Typeclass
  name::Symbol
  type_params::Vector{Symbol}
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
    _ => throw(ParseError("Ill-formed function definition $expr"))
  end
  @match fun_expr begin
    (Expr(:(::), [Expr(:call, args, _), return_type], _) => 
      JuliaFunction(Expr(:call, args...), return_type, impl))
    (Expr(:call, args, _) =>
      JuliaFunction(Expr(:call, args...), Nullable(), impl))
    _ => throw(ParseError("Ill-formed function header $fun_expr"))
  end
end

""" Parse signature of Julia function.
"""
function parse_function_sig(call_expr::Expr)::JuliaFunctionSig
  name, args = @match call_expr begin
    Expr(:call, [name::Symbol, args...], _) => (name, args)
    _ => throw(ParseError("Ill-formed function signature $call_expr"))
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

""" Replace types in signature of Julia function.
"""
function replace_types(bindings::Dict, f::JuliaFunction)::JuliaFunction
  JuliaFunction(
    replace_types(bindings, f.call_expr),
    isnull(f.return_type) ?
      Nullable() : replace_symbols(bindings, get(f.return_type)),
    f.impl) # Don't touch the function body.
end

""" Replace types in Julia expression.
"""
function replace_types(bindings::Dict, expr::Union{Symbol,Expr})
  recurse(expr) = replace_types(bindings, expr)
  @match expr begin
    (Expr(:(::), [fst, snd], _) => 
      Expr(:(::), [recurse(fst), replace_symbols(bindings, snd)]...))
    Expr(head, args, _) => Expr(head, map(recurse, args)...)
    _ => expr
  end
end

""" Replace symbols (occuring anywhere) in a Julia expression.
"""
function replace_symbols(bindings::Dict, expr)
  recurse(expr) = replace_symbols(bindings, expr)
  @match expr begin
    Expr(head, args, _) => Expr(head, map(recurse,args)...)
    sym::Symbol => get(bindings, sym, sym)
    _ => expr
  end
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
    _ => throw(ParseError("Ill-formed raw expression $expr"))
  end
  expr # Return the expression unmodified. This function just checks syntax.
end

""" Parse context for term or type in a GAT.
"""
function parse_context(expr::Expr)::Context
  @assert expr.head == :tuple
  context = Context()
  for arg in expr.args
    name, typ = @match arg begin
      Expr(:(::), [name::Symbol, typ], _) => (name, parse_raw_expr(typ))
      _ => throw(ParseError("Ill-formed context expression $expr"))
    end
    push_context!(context, name, typ)
  end
  return context
end
function push_context!(context, name, expr)
  if haskey(context, name)
    throw(ParseError("Name $name already defined"))
  end
  context[name] = expr
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
          push_context!(context, name, parse_raw_expr(typ))
          name
        end
        name::Symbol => name
        _ => throw(ParseError("Ill-formed type/term parameter $param"))
      end for param in params ]
  end
  
  @match cons_expr begin
    (Expr(:(::), [name::Symbol, :TYPE], _)
      => TypeConstructor(name, [], context))
    (Expr(:(::), [Expr(:call, [name::Symbol, params...], _), :TYPE], _)
      => TypeConstructor(name, parse_params(params), context))
    (Expr(:(::), [Expr(:call, [name::Symbol, params...], _), typ], _)
      => TermConstructor(name, parse_params(params), parse_raw_expr(typ), context))
    _ => throw(ParseError("Ill-formed type/term constructor $cons_expr"))
  end
end

""" Generate abstract type definition from a GAT type constructor.
"""
function gen_abstract_type(cons::TypeConstructor)::Expr
  stub_name = GlobalRef(GAT, :Stub)
  :(abstract $(cons.name) <: $stub_name)
end

""" Replace names of type constructors in a GAT.
"""
function replace_types(bindings::Dict, sig::Signature)::Signature
  Signature([ replace_types(bindings, t) for t in sig.types ],
            [ replace_types(bindings, t) for t in sig.terms ])
end
function replace_types(bindings::Dict, cons::TypeConstructor)::TypeConstructor
  TypeConstructor(replace_symbols(bindings, cons.name),
                  cons.params,
                  replace_types(bindings, cons.context))
end
function replace_types(bindings::Dict, cons::TermConstructor)::TermConstructor
  TermConstructor(cons.name, cons.params,
                  replace_symbols(bindings, cons.typ),
                  replace_types(bindings, cons.context))
end
function replace_types(bindings::Dict, context::Context)::Context
  GAT.Context(((name => @match expr begin
    (Expr(:call, [sym::Symbol, args...], _) => 
      Expr(:call, replace_symbols(bindings, sym), args...))
    sym::Symbol => replace_symbols(bindings, sym)
  end) for (name, expr) in context))
end

""" Remove type parameters from dependent type.
"""
function strip_type(expr)::Symbol
  @match expr begin
    Expr(:call, [head::Symbol, args...], _) => head
    sym::Symbol => sym
  end
end

# Signatures
############

""" TOOD
"""
macro signature(head, body)
  # Parse signature header.
  head = parse_signature_head(head)
  @assert length(head.base) <= 1 "Multiple signature extension not supported"
  if length(head.base) == 1
    base_name, base_params = head.base[1].name, head.base[1].params
    @assert all(p in head.main.params for p in base_params)
  else 
    base_name, base_params = nothing, []
  end
    
  # Parse signature body: GAT types/terms and extra Julia functions.
  types, terms, functions = parse_signature_body(body)
  signature = Signature(types, terms)
  class = Typeclass(head.main.name, head.main.params, signature, functions)
  
  # We must generate and evaluate the code at *run time* because the base
  # signature, if specified, is not available at *parse time*.
  expr = :(signature_code($class, $(esc(base_name)), $base_params))
  Expr(:call, esc(:eval), expr)
end
function signature_code(main_class, base_mod, base_params)
  # Add types/terms/functions from base class, if provided.
  if base_mod == nothing
    class = main_class
  else
    base_class = base_mod.class()
    bindings = Dict(zip(base_class.type_params, base_params))
    main_sig = main_class.signature
    base_sig = replace_types(bindings, base_class.signature)
    sig = Signature([base_sig.types; main_sig.types],
                    [base_sig.terms; main_sig.terms])
    functions = [ [ replace_types(bindings, f) for f in base_class.functions ]; 
                  main_class.functions ]
    class = Typeclass(main_class.name, main_class.type_params, sig, functions)
  end
  
  # Generate module: signature definition and method stubs.
  signature = class.signature
  all_functions = [ interface(signature); class.functions ]
  body = Expr(:block, [
    Expr(:export, [cons.name for cons in signature.types]...);
    Expr(:export, unique(f.call_expr.args[1] for f in all_functions)...);
  
    map(gen_abstract_type, signature.types);
    map(gen_function, all_functions);
    
    :(class() = $(class));
  ]...)
  # Modules must be at top level:
  # https://github.com/JuliaLang/julia/issues/21009
  mod = Expr(:module, true, class.name, body)
  Expr(:toplevel, mod)
end

function parse_signature_head(expr::Expr)::SignatureHead
  parse = parse_signature_binding
  @match expr begin
    (Expr(:(=>), [Expr(:tuple, bases, _), main], _)
      => SignatureHead(parse(main), map(parse, bases)))
    Expr(:(=>), [base, main], _) => SignatureHead(parse(main), [parse(base)])
    _ => SignatureHead(parse(expr))
  end
end

function parse_signature_binding(expr::Expr)::SignatureBinding
  @match expr begin
    Expr(:call, [name::Symbol, params...], _) => SignatureBinding(name, params)
    _ => throw(ParseError("Ill-formed signature binding $expr"))
  end
end

""" Parse the body of a GAT signature declaration.
"""
function parse_signature_body(expr::Expr)
  @assert expr.head == :block
  types, terms, funs = OrderedDict(), [], []
  for elem in filter_line(expr).args
    if elem.head in (:(::), :call)
      cons = parse_constructor(elem)
      if isa(cons, TypeConstructor)
        if haskey(types, cons.name)
          throw(ParseError("Duplicate type constructor $elem"))
        else
          types[cons.name] = cons end
      else
        push!(terms, cons) end
    elseif elem.head in (:(=), :function)
      push!(funs, parse_function(elem))
    else
      throw(ParseError("Ill-formed signature element $elem"))
    end
  end
  return (collect(values(types)), terms, funs)
end

""" Julia functions for type parameter accessors.
"""
function accessors(sig::Signature)::Vector{JuliaFunction}
  vcat(map(accessors, sig.types)...)
end
function accessors(cons::TypeConstructor)::Vector{JuliaFunction}
  [ JuliaFunction(Expr(:call, p, Expr(:(::), cons.name)),
                  strip_type(cons.context[p]))
    for p in cons.params ]
end

""" Julia functions for term constructors of GAT.
"""
function constructors(sig::Signature)::Vector{JuliaFunction}
  map(constructor, sig.terms)
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
function interface(class::Typeclass)::Vector{JuliaFunction}
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
  bindings = Dict(zip(class.type_params, instance_types))
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

end
