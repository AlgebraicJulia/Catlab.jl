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
export Expression, PathExpression, Statement, GraphStatement, Property,
  Document, Picture, Scope, Coordinate, Node, NodeCoordinate, Edge, EdgeNode,
  PathOperation, Graph, GraphScope, GraphNode, GraphEdge, MatrixNode, pprint

using Compat
using AutoHashEquals

# AST
#####

abstract type Expression end
abstract type PathExpression <: Expression end
abstract type Statement <: Expression end
abstract type GraphStatement <: Expression end

@auto_hash_equals struct Property <: Expression
  key::String
  value::Union{String,Vector{Property},Nothing}
  
  Property(key::String, value=nothing) = new(key, value)
end

as_property(prop::Property) = prop
as_property(pair::Pair) = as_property(first(pair), last(pair))
as_property(key::String, value::Union{String,Nothing}=nothing) = Property(key, value)
as_property(key::String, values::AbstractVector) = Property(key, as_properties(values))

as_properties(props::Vector{Property}) = props
as_properties(props) = Property[ as_property(prop) for prop in props ]

@auto_hash_equals struct Picture <: Expression
  stmts::Vector{Statement}
  props::Vector{Property}
  
  Picture(stmts::Vararg{Statement}; props=Property[]) = new([stmts...], props)
end

@auto_hash_equals struct Document <: Expression
  picture::Picture
  libraries::Vector{String}
  packages::Vector{String}
  
  Document(picture::Picture; libraries=String[], packages=String[]) =
    new(picture, libraries, packages)
end

@auto_hash_equals struct Scope <: Statement
  stmts::Vector{Statement}
  props::Vector{Property}
  
  Scope(stmts::Vararg{Statement}; props=Property[]) = new([stmts...], props)
end

@auto_hash_equals struct Coordinate <: PathExpression
  x::String
  y::String
  
  Coordinate(x::String, y::String) = new(x, y)
  Coordinate(x::Number, y::Number) = new(string(x), string(y))
end

@auto_hash_equals struct Node <: Statement
  # FIXME: Name is optional, according to TikZ manual.
  name::String
  props::Vector{Property}
  coord::Union{Coordinate,Nothing}
  content::String
  
  Node(name::String; props=Property[], coord=nothing, content="") =
    new(name, props, coord, content)
end

@auto_hash_equals struct NodeCoordinate <: PathExpression
  name::String
end

@auto_hash_equals struct EdgeNode <: PathExpression
  props::Vector{Property}
  content::Union{String,Nothing}
  
  EdgeNode(; props=Property[], content=nothing) = new(props, content)
end

@auto_hash_equals struct Edge <: Statement
  exprs::Vector{PathExpression}
  props::Vector{Property}
  
  Edge(args...; props=Property[]) =
    new([arg isa String ? NodeCoordinate(arg) : arg for arg in args], props)
end

@auto_hash_equals struct PathOperation <: PathExpression
  op::String
  props::Vector{Property}
  
  PathOperation(op::String; props=Property[]) = new(op, props)
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
  name::String
  props::Vector{Property}
  content::Union{String,Nothing}
  
  GraphNode(name::String; props=Property[], content=nothing) =
    new(name, props, content)
end

@auto_hash_equals struct GraphEdge <: GraphStatement
  src::String
  tgt::String
  props::Vector{Property}
  
  GraphEdge(src::String, tgt::String; props=Property[]) =
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
pprint(expr::Expression; kw...) = pprint(stdout, expr; kw...)
pprint(io::IO, expr::Expression; kw...) = pprint(io, expr, 0; kw...)

function pprint(io::IO, doc::Document, n::Int)
  for package in doc.packages
    indent(io, n)
    println(io, "\\usepackage{$package}")
  end
  for library in doc.libraries
    indent(io, n)
    println(io, "\\usetikzlibrary{$library}")
  end
  pprint(io, doc.picture, n)
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
  if !isnothing(node.coord)
    print(io, " at ")
    pprint(io, node.coord)
  end
  print(io, " {$(node.content)};")
end

function pprint(io::IO, edge::Edge, n::Int)
  indent(io, n)
  print(io, "\\path")
  pprint(io, edge.props)
  for expr in edge.exprs
    print(io, " ")
    pprint(io, expr)
  end
  print(io, ";")
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

function pprint(io::IO, node::NodeCoordinate, n::Int)
  print(io, "($(node.name))")
end

function pprint(io::IO, op::PathOperation, n::Int)
  print(io, op.op)
  pprint(io, op.props)
end

function pprint(io::IO, prop::Property, n::Int)
  print(io, prop.key)
  if !isnothing(prop.value)
    print(io, "=")
    if prop.value isa Vector{Property}
      pprint(io, prop.value, nested=true)
    else
      print(io, prop.value)
    end
  end
end

function pprint(io::IO, props::Vector{Property}, n::Int=0; nested::Bool=false)
  if !isempty(props)
    print(io, nested ? "{" : "[")
    for (i, prop) in enumerate(props)
      pprint(io, prop)
      if (i < length(props)) print(io, ",") end
    end
    print(io, nested ? "}" : "]")
  end
end

indent(io::IO, n::Int) = print(io, " "^n)

end
