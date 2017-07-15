""" AST and pretty printer for Graphviz's DOT language.

This module does not provide bindings to the Graphviz library. For that, see
the GraphViz.jl package: https://github.com/Keno/GraphViz.jl

References:

- DOT grammar: http://www.graphviz.org/doc/info/lang.html
- DOT language guide: http://www.graphviz.org/pdf/dotguide.pdf
"""
module Graphviz
export Expression, Statement, Graph, Digraph, Subgraph, Node, Edge, pprint

using DataStructures: OrderedDict

# AST
#####

abstract type Expression end
abstract type Statement <: Expression end

const Attributes = OrderedDict{Symbol,String}

struct Graph <: Expression
  name::String
  directed::Bool
  stmts::Vector{Statement}
  attrs::Attributes
end
Graph(name::String, stmts::Vector{Statement}, attrs::Attributes) = 
  Graph(name, false, stmts, attrs)
Digraph(name::String, stmts::Vector{Statement}, attrs::Attributes) =
  Graph(name, true, stmts, attrs)
Graph(name::String, stmts::Vararg{Statement}; attrs...) =
  Graph(name, false, collect(stmts), Attributes(attrs))
Digraph(name::String, stmts::Vararg{Statement}; attrs...) =
  Graph(name, true, collect(stmts), Attributes(attrs))

struct Subgraph <: Statement
  name::String
  stmts::Vector{Statement}
  attrs::Attributes
end
Subgraph(name::String, stmts::Vararg{Statement}; attrs...) =
  Subgraph(name, collect(stmts), Attributes(attrs))

struct Node <: Statement
  name::String
  attrs::Attributes
end
Node(name::String; attrs...) = Node(name, Attributes(attrs))

struct Edge <: Statement
  src::String
  tgt::String
  attrs::Attributes
end
Edge(src::String, tgt::String; attrs...) = Edge(src, tgt, Attributes(attrs))

# Pretty-print
##############

""" Pretty-print the Graphviz expression.
"""
pprint(expr::Expression) = pprint(STDOUT, expr)
pprint(io::IO, expr::Expression) = pprint(io, expr, 0)

function pprint(io::IO, graph::Graph, n::Int)
  indent(io, n)
  print(io, graph.directed ? "digraph " : "graph ")
  print(io, graph.name)
  println(io, " {")
  pprint_attrs_long(io, graph.attrs, n+2)
  for stmt in graph.stmts
    pprint(io, stmt, n+2, directed=graph.directed)
    println(io)
  end
  indent(io, n)
  println(io, "}")
end

function pprint(io::IO, subgraph::Subgraph, n::Int; directed::Bool=false)
  indent(io, n)
  print(io, "subgraph ")
  print(io, subgraph.name)
  println(io, " {")
  pprint_attrs_long(io, subgraph.attrs, n+2)
  for stmt in subgraph.stmts
    pprint(io, stmt, n+2, directed=directed)
    println(io)
  end
  indent(io, n)
  print(io, "}")
end

function pprint(io::IO, node::Node, n::Int; directed::Bool=false)
  indent(io, n)
  print(io, node.name)
  if !isempty(node.attrs)
    print(io, " [")
    pprint_attrs_short(io, node.attrs)
    print(io, "]")
  end
  print(io, ";")
end

function pprint(io::IO, edge::Edge, n::Int; directed::Bool=false)
  indent(io, n)
  print(io, edge.src)
  print(io, directed ? " -> " : " -- ")
  print(io, edge.tgt)
  if !isempty(edge.attrs)
    print(io, " [")
    pprint_attrs_short(io, edge.attrs)
    print(io, "]")
  end
  print(io, ";")
end

function pprint_attrs_long(io::IO, attrs::Attributes, n::Int)
  for (key, value) in attrs
    indent(io, n)
    print(io, key)
    print(io, " = \"")
    print(io, value)
    println(io, "\";")
  end
end

function pprint_attrs_short(io::IO, attrs::Attributes)
  for (i, (key, value)) in enumerate(attrs)
    if (i > 1) print(io, ",") end
    print(io, key)
    print(io, "=\"")
    print(io, value)
    print(io, "\"")
  end
end

indent(io::IO, n::Int) = print(io, " "^n)

end
