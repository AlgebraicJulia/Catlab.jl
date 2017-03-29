module GAT
export @signature, methodswith

using Base.Meta: show_sexpr
using AutoHashEquals
import DataStructures: OrderedDict
using Match

# Internal data types
#####################

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

@auto_hash_equals immutable JuliaFunction
  call_expr::Expr
  return_type::Nullable{Union{Symbol,Expr}}
  default_impl::Nullable{Expr}
  
  function JuliaFunction(call_expr, return_type=Nullabe(), default_impl=Nullable()) 
    new(call_expr, return_type, default_impl)
  end
end

""" Signature for GAT plus default Julia code for instances.
"""
@auto_hash_equals immutable JuliaSignature
  signature::Signature
  functions::Vector{JuliaFunction}
end

# Julia parsing
###############

""" Parse Julia function declaration into standardized form.
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
  
# GAT parsing
#############

""" Parse a raw expression in a GAT.

A "raw expression" is a just composition of function and constant symbols.
"""
function parse_raw_expr(expr)
  @match expr begin
    Expr(:call, args, _) => map(parse_raw_expr, args)
    head::Symbol => nothing
    _ => throw(ParseError("Ill-formed raw expression $(as_sexpr(expr))"))
  end
  expr
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

function parse_signature_binding(expr::Expr)::SignatureBinding
  @match expr begin
    Expr(:call, [name::Symbol, params...], _) => SignatureBinding(name, params)
    _ => throw(ParseError("Ill-formed signature binding $(as_sexpr(expr))"))
  end
end

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

# Signatures
############

immutable _GAT{T} end

""" TOOD
"""
macro signature(args...)
  # Parse signature: GAT and extra Julia functions.
  head = parse_signature_binding(args[1])
  types, terms, funs = parse_signature_body(args[end])
  sig = Signature(types, terms)
  julia_sig = JuliaSignature(sig, funs)
  
  # Generate code: signature definition and method stubs.
  return esc(:($(head.name) = $julia_sig))
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
  args = [ Expr(:(::), p, strip_type(cons.context[p])) for p in cons.params ]
  call_expr = Expr(:call, cons.name, args...)
  return_type = strip_type(cons.typ)
  JuliaFunction(call_expr, return_type)
end

function interface(sig::JuliaSignature)::Vector{JuliaFunction}
  [ accessors(sig.signature);
    constructors(sig.signature);
    sig.functions ]
end

methodswith(sig::JuliaSignature, args...) = methodswith(_GAT{sig}, args...)

# Utility functions
###################

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

""" Push key-value pair unless there is a key collision.
"""
function push_unique!(collection, key, value)
  if haskey(collection, key)
    throw(ParseError("Name $key already defined"))
  end
  collection[key] = value
end

""" Remove type parameters from dependent type.
"""
function strip_type(expr)::Symbol
  @match expr begin
    Expr(:call, [head::Symbol, args...], _) => head
    sym::Symbol => sym
  end
end

""" Recursively remove type parameters from all dependent types in expression.
"""
function strip_types(expr)
  @match expr begin
    Expr(:(::), [fst, snd], _) => Expr(:(::), [strip_types(fst), strip_type(snd)]...)
    Expr(head, args, _) => Expr(head, map(strip_types, args)...)
    _ => expr
  end
end

end
