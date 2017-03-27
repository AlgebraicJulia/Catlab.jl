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

immutable SignatureCall
  name::Symbol
  params::Vector{Symbol}
end

immutable Signature
  head::SignatureCall
  types::Dict{Symbol,TypeConstructor}
  terms::Dict{Symbol,TermConstructor}
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
    if haskey(context, name)
      throw(ParseError("Duplicate name in context expression $(as_sexpr(expr))"))
    end
    push!(context, name => typ)
  end
  return context
end

function parse_type_constructor(expr::Expr)::TypeConstructor
  @assert expr.head == :type
  name, params = @match expr.args[2] begin
    Expr(:call, [name::Symbol, params...], _) => (name, params)
    name::Symbol => (name, [])
    _ => throw(ParseError("Ill-formed type constructor $(as_sexpr(expr))"))
  end
  context = parse_context(expr.args[3])
  TypeConstructor(name, params, context)
end

function parse_term_constructor(expr::Expr)::TermConstructor
  @assert expr.head == :function
  name, params, typ = @match expr.args[1] begin
    (Expr(:(::), [Expr(:call, [name::Symbol, params...], _), typ], _)
      => (name, params, parse_raw_expr(typ)))
    _ => throw(ParseError("Ill-formed term constructor $(as_sexpr(expr))"))
  end
  context = parse_context(expr.args[2])
  TermConstructor(name, params, typ, context)
end

function parse_signature_call(expr::Expr)::SignatureCall
  @match expr begin
    Expr(:call, [name::Symbol, params...], _) => SignatureCall(name, params)
    _ => throw(ParseError("Ill-formed signature header $(as_sexpr(expr))"))
  end
end

# Macros
########

macro signature(args...)
  head = parse_signature_call(args[1])
  body = filter_line(args[end])
  #println(dump(body))
  return :()
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

""" Remove all :line annotations from an expression.
"""
function filter_line(expr::Expr, recurse::Bool=false)
  args = filter(x -> !(isa(x, Expr) && x.head == :line), expr.args)
  if recurse
    args = [ isa(x, Expr) ? filter_line(x, true) : x for x in args ]
  end
  Expr(expr.head, args...)
end

end
