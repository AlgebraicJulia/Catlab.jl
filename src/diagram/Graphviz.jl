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
using Parameters

# AST
#####

abstract type Expression end
abstract type Statement <: Expression end

const Attributes = OrderedDict{Symbol,String}
const Statements = Vector{Statement}

@with_kw struct Graph <: Expression
  name::String
  directed::Bool
  stmts::Statements=Statements()
  graph_attrs::Attributes=Attributes()
  node_attrs::Attributes=Attributes()
  edge_attrs::Attributes=Attributes()
end

Graph(name::String, stmts::Statements; kw...) =
  Graph(name=name, directed=false, stmts=stmts; kw...)
Digraph(name::String, stmts::Statements; kw...) =
  Graph(name=name, directed=true, stmts=stmts; kw...)
Graph(name::String, stmts::Vararg{Statement}; kw...) =
  Graph(name, collect(stmts); kw...)
Digraph(name::String, stmts::Vararg{Statement}; kw...) =
  Digraph(name, collect(stmts); kw...)

@with_kw struct Subgraph <: Statement
  name::String
  stmts::Statements=Statements()
  graph_attrs::Attributes=Attributes()
  node_attrs::Attributes=Attributes()
  edge_attrs::Attributes=Attributes()
end

Subgraph(name::String, stmts::Statements; kw...) =
  Subgraph(name=name, stmts=stmts, kw...)
Subgraph(name::String, stmts::Vararg{Statement}; kw...) =
  Subgraph(name, collect(stmts); kw...)

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
  pprint_attrs(io, graph.graph_attrs, n+2; pre="graph", post=";\n")
  pprint_attrs(io, graph.node_attrs, n+2; pre="node", post=";\n")
  pprint_attrs(io, graph.edge_attrs, n+2; pre="edge", post=";\n")
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
  pprint_attrs(io, subgraph.graph_attrs, n+2; pre="graph", post=";\n")
  pprint_attrs(io, subgraph.node_attrs, n+2; pre="node", post=";\n")
  pprint_attrs(io, subgraph.edge_attrs, n+2; pre="edge", post=";\n")
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
  pprint_attrs(io, node.attrs)
  print(io, ";")
end

function pprint(io::IO, edge::Edge, n::Int; directed::Bool=false)
  indent(io, n)
  print(io, edge.src)
  print(io, directed ? " -> " : " -- ")
  print(io, edge.tgt)
  pprint_attrs(io, edge.attrs)
  print(io, ";")
end

function pprint_attrs(io::IO, attrs::Attributes, n::Int=0;
                      pre::String="", post::String="")
  if !isempty(attrs)
    indent(io, n)
    print(io, pre)
    print(io, " [")
    for (i, (key, value)) in enumerate(attrs)
      if (i > 1) print(io, ",") end
      print(io, key)
      print(io, "=\"")
      print(io, value)
      print(io, "\"")
    end
    print(io, "]")
    print(io, post)
  end
end

indent(io::IO, n::Int) = print(io, " "^n)

end
