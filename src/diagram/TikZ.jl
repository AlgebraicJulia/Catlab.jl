module TikZ
export Expression, Statement, GraphStatement, Coordinate, Property, 
       PathOperation, Picture, Scope, Node, Edge, EdgeNode, Graph, GraphScope,
       GraphNode, GraphEdge, pprint, spprint, to_tikz

using AutoHashEquals
using Match
import ...Syntax: pprint
import ..Wiring
import ..Wiring: dom, codom

# AST
#####

""" Base class for TikZ abstract syntax tree.

The AST is very incomplete! It is adapted from the (also incomplete) BNF
grammar for TikZ in [TikZit](http://tikzit.sourceforge.net/manual.html).
"""
abstract Expression
abstract Statement <: Expression
abstract GraphStatement <: Expression

@auto_hash_equals immutable Coordinate <: Expression
  x::AbstractString
  y::AbstractString
end

@auto_hash_equals immutable Property <: Expression
  key::AbstractString
  value::Nullable{AbstractString}
  
  Property(key::AbstractString) = new(key, Nullable())
  Property(key::AbstractString, value::AbstractString) = new(key, Nullable(value))
end

@auto_hash_equals immutable PathOperation <: Expression
  op::AbstractString
  props::Vector{Property}
  
  PathOperation(op::AbstractString; props=Property[]) = new(op, props)
end

@auto_hash_equals immutable Picture <: Expression
  stmts::Vector{Statement}
  props::Vector{Property}
  
  Picture(stmts::Vararg{Statement}; props=Property[]) = new([stmts...], props)
end

@auto_hash_equals immutable Scope <: Statement
  stmts::Vector{Statement}
  props::Vector{Property}
  
  Scope(stmts::Vararg{Statement}; props=Property[]) = new([stmts...], props)
end

@auto_hash_equals immutable Node <: Statement
  name::AbstractString
  props::Vector{Property}
  coord::Nullable{Coordinate}
  content::AbstractString
  
  Node(name::AbstractString; props=Property[], coord=Nullable(), content="") =
    new(name, props, coord, content)
end

@auto_hash_equals immutable EdgeNode <: Expression
  props::Vector{Property}
  content::Nullable{AbstractString}
  
  EdgeNode(; props=Property[], content=Nullable()) = new(props, content)
end

@auto_hash_equals immutable Edge <: Statement
  src::AbstractString
  tgt::AbstractString
  op::PathOperation
  props::Vector{Property}
  node::Nullable{EdgeNode}
  
  Edge(src::AbstractString, tgt::AbstractString;
       op=PathOperation("to"), props=Property[], node=Nullable()) =
    new(src, tgt, op, props, node)
end

@auto_hash_equals immutable Graph <: Statement
  stmts::Vector{GraphStatement}
  props::Vector{Property}
  
  Graph(stmts::Vararg{GraphStatement}; props=Property[]) =
    new([stmts...], props)
end

@auto_hash_equals immutable GraphScope <: GraphStatement
  stmts::Vector{GraphStatement}
  props::Vector{Property}
  
  GraphScope(stmts::Vararg{GraphStatement}; props=Property[]) =
    new([stmts...], props)
end

@auto_hash_equals immutable GraphNode <: GraphStatement
  name::AbstractString
  props::Vector{Property}
  content::Nullable{AbstractString}
  
  GraphNode(name::AbstractString; props=Property[], content=Nullable()) =
    new(name, props, content)
end

@auto_hash_equals immutable GraphEdge <: GraphStatement
  src::AbstractString
  tgt::AbstractString
  props::Vector{Property}
  
  GraphEdge(src::AbstractString, tgt::AbstractString; props=Property[]) =
    new(src, tgt, props)
end

# Pretty-print
##############

""" Pretty-print the TikZ expression.
"""
pprint(expr::Expression) = pprint(STDOUT, expr)
pprint(io::IO, expr::Expression) = pprint(io, expr, 0)

""" Pretty-print the TikZ expression as a string.
"""
function spprint(expr::Expression)::AbstractString
  buf = IOBuffer()
  pprint(buf, expr)
  takebuf_string(buf)
end

function pprint(io::IO, pic::Picture, n::Int)
  indent(io, n)
  print(io, "\\begin{tikzpicture}")
  pprint(io, pic.props)
  println(io)
  for stmt in pic.stmts
    pprint(io, stmt, n+2)
    println(io)
  end
  indent(io, n)
  print(io, "\\end{tikzpicture}")
end

function pprint(io::IO, scope::Scope, n::Int)
  indent(io, n)
  print(io, "\\begin{scope}")
  pprint(io, scope.props)
  println(io)
  for stmt in scope.stmts
    pprint(io, stmt, n+2)
    println(io)
  end
  indent(io, n)
  print(io, "\\end{scope}")
end

function pprint(io::IO, node::Node, n::Int)
  indent(io, n)
  print(io, "\\node")
  pprint(io, node.props)
  print(io, " ($(node.name))")
  if !isnull(node.coord)
    print(io, " at ")
    pprint(io, get(node.coord))
  end
  if !isnull(node.content)
    print(io, " {$(node.content)}")
  end
  print(io, ";")
end

function pprint(io::IO, edge::Edge, n::Int)
  indent(io, n)
  print(io, "\\draw")
  pprint(io, edge.props)
  print(io, " ($(edge.src)) ")
  pprint(io, edge.op)
  if !isnull(edge.node)
    print(io, " ")
    pprint(io, get(edge.node))
  end
  print(io, " ($(edge.tgt));")
end

function pprint(io::IO, node::EdgeNode, n::Int)
  print(io, "node")
  pprint(io, node.props)
  if !isnull(node.content)
    print(io, " {$(get(node.content))}")
  end
end

function pprint(io::IO, graph::Graph, n::Int)
  indent(io, n)
  print(io, "\\graph")
  pprint(io, graph.props)
  println(io, "{")
  for stmt in graph.stmts
    pprint(io, stmt, n+2)
    println(io)
  end
  indent(io, n)
  print(io, "};")
end

function pprint(io::IO, scope::GraphScope, n::Int)
  indent(io, n)
  print(io, "{")
  pprint(io, scope.props)
  println(io)
  for stmt in scope.stmts
    pprint(io, stmt, n+2)
    println(io)
  end
  indent(io, n)
  print(io, "};")
end

function pprint(io::IO, node::GraphNode, n::Int)
  indent(io, n)
  print(io, node.name)
  if !isnull(node.content)
    print(io, "/\"$(get(node.content))\"")
  end
  if !isempty(node.props)
    print(io, " ")
    pprint(io, node.props)
  end
  print(io, ";")
end

function pprint(io::IO, node::GraphEdge, n::Int)
  indent(io ,n)
  print(io, "$(node.src) ->")
  pprint(io, node.props)
  print(io, " $(node.tgt);")
end

function pprint(io::IO, coord::Coordinate, n::Int)
  print(io, "($(coord.x),$(coord.y))")
end

function pprint(io::IO, op::PathOperation, n::Int)
  print(io, op.op)
  pprint(io, op.props)
end

function pprint(io::IO, prop::Property, n::Int)
  print(io, prop.key)
  if !isnull(prop.value)
    print(io, "=")
    print(io, get(prop.value))
  end
end

function pprint(io::IO, props::Vector{Property}, n::Int=0)
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

end
