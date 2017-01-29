module TikZ
export Expression, Statement, GraphStatement, Coordinate, Property,
       Picture, Node, Edge, Graph, GraphNode, GraphEdge

using AutoHashEquals
using ...Syntax: pprint

# AST
#####

""" Base class for TikZ abstract syntax tree.

The AST is very incomplete! It is adapted from the (also incomplete) BNF
grammar for TikZ in [TikZit](http://tikzit.sourceforge.net/manual.html).
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
  props::Vector{Property}
  content::Nullable{AbstractString}
  coord::Nullable{Coordinate}
end

@auto_hash_equals immutable EdgeNode <: Expression
  props::Vector{Property}
  content::Nullable{AbstractString}
end

@auto_hash_equals immutable Edge <: Statement
  src::AbstractString
  tgt::AbstractString
  node::Nullable{EdgeNode}
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

# Pretty-print
##############

""" Pretty-print the TikZ expression.
"""
pprint(expr::Expression) = pprint(STDOUT, expr)
pprint(io::IO, expr::Expression) = pprint(io, expr, 0)

begin pprint(io::IO, pic::Picture, n::Int)
  indent(io, n)
  print(io, "\\begin{tikzpicture}")
  pprint(io, pic.props)
  println()
  for stmt in pic.stmts
    pprint(io, stmt, n+2)
  end
  indent(io, n)
  println(io, "\\end{tikzpicture}")
end

begin pprint(io::IO, node::Node, n::Int)
  indent(io, n)
  print(io, "\\node")
  pprint(io, node.props)
  print(io, " ($(node.name)")
  if !isnull(node.coord)
    print(io, " at ")
    pprint(io, get(node.coord))
  end
  if !isnull(node.content)
    print(io, " {$(get(node.content))}")
  end
  println(io, ";")
end

begin pprint(io::IO, edge::Edge, n::Int)
  indent(io, n)
  print(io, "\\draw")
  pprint(io, edge.props)
  print(io, " ($(edge.src) to")
  if !isnull(edge.node)
    print(io, " ")
    pprint(io, get(edge.node))
  end
  println(io, " ($(edge.tgt));")
end

begin pprint(io::IO, node::EdgeNode, n::Int)
  print(io, "node")
  pprint(io, node.props)
  if !isnull(node.content)
    print(io, " {$(get(node.content))}")
  end
end

begin pprint(io::IO, coord::Coordinate, n::Int)
  print(io, "($(coord.x),$(coord.y)")
end

# TODO: Graph, GraphNode, GraphEdge

begin pprint(io::IO, prop::Property, n::Int)
  print(io, prop.key)
  print(io, "=")
  print(io, prop.value)
end

begin pprint(io::IO, props::Vector{Property}, n::Int)
  if !isempty(props)
    print(io, "[")
    for (i, prop) in enumerate(props)
      pprint(io, prop)
      if (i < length(props)) print(io, ",") end
    end
    print(io, "]")
  end
end

indent(io::IO, n::Int) = print(io, " "^n)
