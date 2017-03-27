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

immutable JuliaFunction
  call_expr::Expr
  return_type::Nullable{Expr}
  default_impl::Nullable{Expr}
end

""" Signature for GAT plus default Julia code for instances.
"""
type JuliaClass
  signature::Signature
  functions::Vector{JuliaFunction}
end
  
# Julia expression parsing
##########################

function parse_raw_expr(expr)::RawExpr
  @match expr begin
    Expr(:call, [head::Symbol, args...], _) => RawExpr(head, map(parse_raw_expr, args))
    head::Symbol => RawExpr(head, [])
    _ => throw(ParseError("Ill-formed raw expression $(as_sexpr(expr))"))
  end
end

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
    _ => throw(ParseError("Ill-formed term constructor $(as_sexpr(cons_expr))"))
  end
end

function parse_signature_binding(expr::Expr)::SignatureBinding
  @match expr begin
    Expr(:call, [name::Symbol, params...], _) => SignatureBinding(name, params)
    _ => throw(ParseError("Ill-formed signature header $(as_sexpr(expr))"))
  end
end

function parse_signature_body(expr::Expr)
  @assert expr.head == :block
  types, terms = OrderedDict(), OrderedDict()
  for elem in filter_line(expr).args
    cons = parse_constructor(elem)
    @match cons begin
      cons::TypeConstructor => push_unique!(types, cons.name, cons)
      cons::TermConstructor => push_unique!(terms, cons.name, cons)
    end
  end
  return (types, terms)
end

# Macros
########

""" TOOD
"""
macro signature(args...)
  head = parse_signature_binding(args[1])
  types, terms = parse_signature_body(args[end])
  sig = Signature(head, types, terms)
  return esc(:($(sig.head.name) = $sig))
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
function filter_line(expr::Expr)
  args = filter(x -> !(isa(x, Expr) && x.head == :line), expr.args)
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
