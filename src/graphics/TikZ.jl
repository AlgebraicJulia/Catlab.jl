module TikZ
export Expression, Statement, GraphStatement, Coordinate, Property,
       Picture, Node, Edge, Graph, GraphNode, GraphEdge

using AutoHashEquals

# AST
#####

""" Base class for TikZ abstract syntax tree.

Adapted from partial CFG for TikZ in TikZit:
  http://tikzit.sourceforge.net/manual.html
"""
abstract Expression
abstract Statement <: Expression
abstract GraphStatement <: Statement

@auto_hash_equals immutable Coordinate <: Expression
  x::AbstractString
  y::AbstractString
end

@auto_hash_equals immutable Property <: Expression
  key::AbstractString
  value::AbstractString
end

@auto_hash_equals immutable Picture <: Expression
  stmts::Vector{Statement}
  props::Vector{Property}
end

@auto_hash_equals immutable Node <: Statement
  name::AbstractString
  content::AbstractString
  coord::Coordinate
  props::Vector{Property}
end

@auto_hash_equals immutable Edge <: Statement
  src::AbstractString
  tgt::AbstractString
  node::Nullable{Node}
  props::Vector{Property}
end

@auto_hash_equals immutable Graph <: Statement
  stmts::Vector{GraphStatement}
  props::Vector{Property}
end

@auto_hash_equals immutable GraphNode <: GraphStatement
  name::AbstractString
  content::AbstractString
  props::Vector{Property}
end

@auto_hash_equals immutable GraphEdge <: GraphStatement
  src::AbstractString
  tgt::AbstractString
  props::Vector{Property}
end

end
