module GAT
export @signature

using Base.Meta: show_sexpr
using AutoHashEquals
import DataStructures: OrderedDict
using Match

# Internal types
################

@auto_hash_equals immutable RawExpr
  head::Symbol
  args::Vector{RawExpr}
end

typealias Context OrderedDict{Symbol,RawExpr}

@auto_hash_equals immutable TypeConstructor
  name::Symbol
  params::Vector{Symbol}
  context::Context
end

@auto_hash_equals immutable TermConstructor
  name::Symbol
  params::Vector{Symbol}
  typ::RawExpr
  context::Context
end

@auto_hash_equals immutable SignatureBinding
  name::Symbol
  params::Vector{Symbol}
end

""" Signature for a generalized algebraic theory (GAT).
"""
@auto_hash_equals immutable Signature
  head::SignatureBinding
  types::OrderedDict{Symbol,TypeConstructor}
  terms::OrderedDict{Symbol,TermConstructor}
end

@auto_hash_equals immutable JuliaFunction
  call_expr::Expr
  return_type::Nullable{Union{Symbol,Expr}}
  default_impl::Nullable{Expr}
end

""" Signature for GAT plus default Julia code for instances.
"""
type JuliaSignature
  signature::Signature
  functions::Vector{JuliaFunction}
end
  
# Julia expression parsing
##########################

""" Parse a raw expression in a GAT.

A "raw expression" is a just composition of function and constant symbols.
"""
function parse_raw_expr(expr)::RawExpr
  @match expr begin
    (Expr(:call, [head::Symbol, args...], _)
      => RawExpr(head, map(parse_raw_expr, args)))
    head::Symbol => RawExpr(head, [])
    _ => throw(ParseError("Ill-formed raw expression $(as_sexpr(expr))"))
  end
end

""" Parse context for term or type in a GAT.
"""
function parse_context(expr::Expr)::Context
  @assert expr.head == :block
  context = OrderedDict()
  for arg in filter_line(expr).args
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
  cons_expr, context = @match expr begin
    Expr(:call, [:<=, inner, context], _) => (inner, parse_context(context))
    _ => (expr, Context())
  end
  @match cons_expr begin
    (Expr(:(::), [name::Symbol, :TYPE], _)
      => TypeConstructor(name, [], context))
    (Expr(:(::), [Expr(:call, [name::Symbol, params...], _), :TYPE], _)
      => TypeConstructor(name, params, context))
    (Expr(:(::), [Expr(:call, [name::Symbol, params...], _), typ], _)
      => TermConstructor(name, params, parse_raw_expr(typ), context))
    _ => throw(ParseError("Ill-formed type/term constructor $(as_sexpr(cons_expr))"))
  end
end

""" Parse a Julia function into standardized form.
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

# Macros
########

""" TOOD
"""
macro signature(args...)
  head = parse_signature_binding(args[1])
  types, terms, funs = parse_signature_body(args[end])
  sig = Signature(head, types, terms)
  julia_sig = JuliaSignature(sig, funs)
  return esc(:($(sig.head.name) = $julia_sig))
end

# Utility functions
###################

""" Convert Julia expression to S-expression.
"""
function as_sexpr(expr)::AbstractString
  io = IOBuffer()
  show_sexpr(io, expr)
  takebuf_string(io)
end

""" Remove all :line annotations from a Julia expression. Not recursive.
"""
function filter_line(expr::Expr; recurse::Bool=false)
  args = filter(x -> !(isa(x, Expr) && x.head == :line), expr.args)
  if recurse
    args = [ isa(x,Expr) ? filter_line(x,recurse=true) : x for x in args ]
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

end
