""" AST and pretty printer for TikZ.

This module does not provide bindings to the TikZ LaTeX package. For that, see
the TikzPictures.jl package: https://github.com/sisl/TikzPictures.jl

The AST is large but still incomplete! It supports:

- Nodes (`\\node`) and edges (`\\draw`)
- Nodes along edges (`\\draw ... node ...`)
- Graphs (`\\graph`)
- Matrices (`\\matrix`)
- Scopes and nested pictures

The AST is adapted from the (also incomplete) BNF grammar for TikZ in
[TikZit](http://tikzit.sourceforge.net/manual.html).
"""
module TikZ
export Expression, Statement, GraphStatement, Coordinate, Property,
  PathOperation, Picture, Scope, Node, Edge, EdgeNode, Graph, GraphScope,
  GraphNode, GraphEdge, MatrixNode, pprint

using Compat
using AutoHashEquals

# AST
#####

abstract type Expression end
abstract type Statement <: Expression end
abstract type GraphStatement <: Expression end

@auto_hash_equals struct Coordinate <: Expression
  x::AbstractString
  y::AbstractString
  
  Coordinate(x::AbstractString, y::AbstractString) = new(x, y)
  Coordinate(x::Number, y::Number) = new(string(x), string(y))
end

@auto_hash_equals struct Property <: Expression
  key::AbstractString
  value::Union{AbstractString,Nothing}
  
  Property(key::AbstractString, value=nothing) = new(key, value)
end

@auto_hash_equals struct PathOperation <: Expression
  op::AbstractString
  props::Vector{Property}
  
  PathOperation(op::AbstractString; props=Property[]) = new(op, props)
end

@auto_hash_equals struct Picture <: Expression
  stmts::Vector{Statement}
  props::Vector{Property}
  
  Picture(stmts::Vararg{Statement}; props=Property[]) = new([stmts...], props)
end

@auto_hash_equals struct Scope <: Statement
  stmts::Vector{Statement}
  props::Vector{Property}
  
  Scope(stmts::Vararg{Statement}; props=Property[]) = new([stmts...], props)
end

@auto_hash_equals struct Node <: Statement
  # FIXME: Name is optional, according to TikZ manual.
  name::AbstractString
  props::Vector{Property}
  coord::Union{Coordinate,Nothing}
  # Allow nested pictures even though TikZ does not "officially" support them.
  content::Union{AbstractString,Picture}
  
  Node(name::AbstractString; props=Property[], coord=nothing, content="") =
    new(name, props, coord, content)
end

@auto_hash_equals struct EdgeNode <: Expression
  props::Vector{Property}
  content::Union{AbstractString,Nothing}
  
  EdgeNode(; props=Property[], content=nothing) = new(props, content)
end

@auto_hash_equals struct Edge <: Statement
  src::AbstractString
  tgt::AbstractString
  op::PathOperation
  props::Vector{Property}
  node::Union{EdgeNode,Nothing}
  
  Edge(src::AbstractString, tgt::AbstractString;
       op=PathOperation("to"), props=Property[], node=nothing) =
    new(src, tgt, op, props, node)
end

@auto_hash_equals struct Graph <: Statement
  stmts::Vector{GraphStatement}
  props::Vector{Property}
  
  Graph(stmts::Vararg{GraphStatement}; props=Property[]) =
    new([stmts...], props)
end

@auto_hash_equals struct GraphScope <: GraphStatement
  stmts::Vector{GraphStatement}
  props::Vector{Property}
  
  GraphScope(stmts::Vararg{GraphStatement}; props=Property[]) =
    new([stmts...], props)
end

@auto_hash_equals struct GraphNode <: GraphStatement
  name::AbstractString
  props::Vector{Property}
  content::Union{AbstractString,Nothing}
  
  GraphNode(name::AbstractString; props=Property[], content=nothing) =
    new(name, props, content)
end

@auto_hash_equals struct GraphEdge <: GraphStatement
  src::AbstractString
  tgt::AbstractString
  props::Vector{Property}
  
  GraphEdge(src::AbstractString, tgt::AbstractString; props=Property[]) =
    new(src, tgt, props)
end

@auto_hash_equals struct MatrixNode <: Statement
  stmts::Matrix{Vector{Statement}}
  props::Vector{Property}
  
  MatrixNode(stmts::Matrix; props=Property[]) = new(stmts, props)
end

# Pretty-print
##############

""" Pretty-print the TikZ expression.
"""
pprint(expr::Expression) = pprint(stdout, expr)
pprint(io::IO, expr::Expression) = pprint(io, expr, 0)

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
  if !isnothing(node.coord)
    print(io, " at ")
    pprint(io, node.coord)
  end
  if isa(node.content, Picture)
    println(io, " {")
    pprint(io, node.content, n+2)
    println(io)
    indent(io, n)
    print(io, "}")
  else
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
  if !isnothing(edge.node)
    print(io, " ")
    pprint(io, edge.node)
  end
  print(io, " ($(edge.tgt));")
end

function pprint(io::IO, node::EdgeNode, n::Int)
  print(io, "node")
  pprint(io, node.props)
  if !isnothing(node.content)
    print(io, " {$(node.content)}")
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
  if !isnothing(node.content)
    print(io, "/\"$(node.content)\"")
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

function pprint(io::IO, matrix::MatrixNode, ind::Int)
  indent(io, ind)
  print(io, "\\matrix")
  pprint(io, matrix.props)
  println(io, "{")
  m,n = size(matrix.stmts)
  for i = 1:m
    for j = 1:n
      p = length(matrix.stmts[i,j])
      for k = 1:p
        pprint(io, matrix.stmts[i,j][k], ind+2)
        if (k < p) println(io) end
      end
      if (j < n) println(io, " &") end
    end
    println(io, " \\\\")
  end
  indent(io, ind)
  print(io, "};")
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
  if !isnothing(prop.value)
    print(io, "=")
    print(io, prop.value)
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
