""" AST and pretty printer for Graphviz's DOT language.

References:

- DOT grammar: http://www.graphviz.org/doc/info/lang.html
- DOT language guide: http://www.graphviz.org/pdf/dotguide.pdf
"""
module Graphviz
export Expression, Statement, Attributes, Graph, Digraph, Subgraph,
  Node, NodeID, Edge, pprint, run_graphviz, to_graphviz

using DataStructures: OrderedDict
import LightGraphs, MetaGraphs
using LightGraphs: edges, vertices, src, dst
using MetaGraphs: get_prop, props
using Parameters

# AST
#####

abstract type Expression end
abstract type Statement <: Expression end

""" AST type for Graphviz's "HTML-like" node labels.

The HTML is represented as an atomic string, for now.
"""
struct Html
  content::String
end
Base.print(io::IO, html::Html) = print(io, html.content)

const AttributeValue = Union{String,Html}
const Attributes = OrderedDict{Symbol,AttributeValue}

sorted_attrs(d::AbstractDict) = Attributes(k => d[k] for k in sort!(collect(keys(d))))

@with_kw_noshow struct Graph <: Expression
  name::String
  directed::Bool
  stmts::Vector{Statement}=Statement[]
  graph_attrs::Attributes=Attributes()
  node_attrs::Attributes=Attributes()
  edge_attrs::Attributes=Attributes()
end

Graph(name::String, stmts::Vector{Statement}; kw...) =
  Graph(; name=name, directed=false, stmts=stmts, kw...)
Graph(name::String, stmts::Vararg{Statement}; kw...) =
  Graph(; name=name, directed=false, stmts=collect(stmts), kw...)
Digraph(name::String, stmts::Vector{Statement}; kw...) =
  Graph(; name=name, directed=true, stmts=stmts, kw...)
Digraph(name::String, stmts::Vararg{Statement}; kw...) =
  Graph(; name=name, directed=true, stmts=collect(stmts), kw...)

@with_kw_noshow struct Subgraph <: Statement
  name::String="" # Subgraphs can be anonymous
  stmts::Vector{Statement}=Statement[]
  graph_attrs::Attributes=Attributes()
  node_attrs::Attributes=Attributes()
  edge_attrs::Attributes=Attributes()
end

Subgraph(stmts::Vector{Statement}; kw...) = Subgraph(; stmts=stmts, kw...)
Subgraph(stmts::Vararg{Statement}; kw...) = Subgraph(; stmts=collect(stmts), kw...)
Subgraph(name::String, stmts::Vector{Statement}; kw...) =
  Subgraph(; name=name, stmts=stmts, kw...)
Subgraph(name::String, stmts::Vararg{Statement}; kw...) =
  Subgraph(; name=name, stmts=collect(stmts), kw...)

struct Node <: Statement
  name::String
  attrs::Attributes
end
Node(name::String, attrs::Dict) = Node(name, sorted_attrs(attrs))
Node(name::String; attrs...) = Node(name, Attributes(attrs))

struct NodeID <: Expression
  name::String
  port::String
  anchor::String
  NodeID(name::String, port::String="", anchor::String="") = new(name, port, anchor)
end

struct Edge <: Statement
  path::Vector{NodeID}
  attrs::Attributes
end
Edge(path::Vector{String}, attrs) = Edge(map(NodeID, path), attrs)
Edge(path::Vector{NodeID}, attrs::Dict) = Edge(path, sorted_attrs(attrs))
Edge(path::Vararg{String}; attrs...) = Edge(map(NodeID, collect(path)), Attributes(attrs))
Edge(path::Vector{String}; attrs...) = Edge(map(NodeID, path), Attributes(attrs))
Edge(path::Vararg{NodeID}; attrs...) = Edge(collect(path), Attributes(attrs))
Edge(path::Vector{NodeID}; attrs...) = Edge(path, Attributes(attrs))

# Bindings
##########

""" Run a Graphviz program.

Assumes that Graphviz is installed on the local system and invokes Graphviz
through its command-line interface.

For bindings to the Graphviz C API, see the the GraphViz.jl package
(https://github.com/Keno/GraphViz.jl). GraphViz.jl is unmaintained at the time
of this writing.
"""
function run_graphviz(graph::Graph; prog::String="dot", format::String="json0")
  gv = open(`$prog -T$format`, "r+")
  pprint(gv.in, graph)
  close(gv.in)
  result = read(gv.out, String)
  if !success(gv)
    error("Graphviz $prog failed with exit code $(gv.exitcode) and signal $(gv.termsignal)")
  end
  result
end

function Base.show(io::IO, ::MIME"image/svg+xml", graph::Graph)
  println(io, run_graphviz(graph, format="svg"))
end

# MetaGraphs
############

""" Convert an attributed graph (MetaGraph) to a Graphviz graph.

This method is usually more convenient than direct AST manipulation for creating
Graphviz graphs. It supports graphs that are directed or undirected, simple or
multi-edged. For more advanced features, like nested subgraphs, you must use
the Graphviz AST directly.
"""
function to_graphviz(g::MetaGraphs.AbstractMetaGraph; multigraph::Bool=false)::Graph
  gv_name(v::Int) = "n$v"
  gv_path(e::LightGraphs.Edge) = [gv_name(src(e)), gv_name(dst(e))]

  # Add Graphviz node for each vertex.
  stmts = Graphviz.Statement[]
  for v in vertices(g)
    push!(stmts, Node(gv_name(v), props(g, v)))
  end

  # Add Graphviz edge for each (multi)edge.
  if multigraph
    for e in edges(g)
      path = gv_path(e)
      append!(stmts, [ Edge(path, attrs) for attrs in get_prop(g, e, :edges) ])
    end
  else
    for e in edges(g)
      push!(stmts, Edge(gv_path(e), props(g, e)))
    end
  end

  attrs = props(g)
  Graph(
    name = get(attrs, :name, "G"),
    directed = LightGraphs.is_directed(g),
    stmts = stmts,
    graph_attrs = Graphviz.Attributes(get(attrs, :graph, Dict())),
    node_attrs = Graphviz.Attributes(get(attrs, :node, Dict())),
    edge_attrs = Graphviz.Attributes(get(attrs, :edge, Dict())),
  )
end

# Pretty-print
##############

""" Pretty-print the Graphviz expression.
"""
pprint(expr::Expression) = pprint(stdout, expr)
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
  if isempty(subgraph.name)
    println(io, "{")
  else
    print(io, "subgraph ")
    print(io, subgraph.name)
    println(io, " {")
  end
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

function pprint(io::IO, node::NodeID, n::Int)
  print(io, node.name)
  if !isempty(node.port)
    print(io, ":")
    print(io, node.port)
  end
  if !isempty(node.anchor)
    print(io, ":")
    print(io, node.anchor)
  end
end

function pprint(io::IO, edge::Edge, n::Int; directed::Bool=false)
  indent(io, n)
  for (i, node) in enumerate(edge.path)
    if i > 1
      print(io, directed ? " -> " : " -- ")
    end
    pprint(io, node, n)
  end
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
      print(io, "=")
      print(io, isa(value, Html) ? "<" : "\"")
      print(io, value)
      print(io, isa(value, Html) ? ">" : "\"")
    end
    print(io, "]")
    print(io, post)
  end
end

indent(io::IO, n::Int) = print(io, " "^n)

end
