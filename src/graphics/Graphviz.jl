""" AST and pretty printer for Graphviz's DOT language.

References:

- DOT grammar: http://www.graphviz.org/doc/info/lang.html
- DOT language guide: http://www.graphviz.org/pdf/dotguide.pdf
"""
module Graphviz
export Expression, Statement, Attributes, Graph, Digraph, Subgraph,
  Node, NodeID, Edge, pprint, parse_graphviz, run_graphviz, to_graphviz

using Compat
using DataStructures: OrderedDict
import LightGraphs, MetaGraphs
using LightGraphs: add_edge!, add_vertex!, edges, vertices, src, dst
using MetaGraphs: get_prop, props, set_prop!, set_props!
using Parameters
using StaticArrays: StaticVector, SVector

# AST
#####

abstract type Expression end
abstract type Statement <: Expression end

""" AST type for Graphviz's "HTML-like" node labels.

For now, the HTML content is just a string.
"""
struct Html
  content::String
end
Base.print(io::IO, html::Html) = print(io, html.content)

const AttributeValue = Union{String,Html}
const Attributes = OrderedDict{Symbol,AttributeValue}

as_attributes(attrs::Attributes) = attrs
as_attributes(d::OrderedDict) = Attributes(Symbol(k) => d[k] for k in keys(d))
as_attributes(d::AbstractDict) =
  Attributes(Symbol(k) => d[k] for k in sort!(collect(keys(d))))

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
Node(name::String, attrs::AbstractDict) = Node(name, as_attributes(attrs))
Node(name::String; attrs...) = Node(name, attrs)

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
Edge(path::Vector{NodeID}, attrs::AbstractDict) = Edge(path, as_attributes(attrs))
Edge(path::Vector{NodeID}; attrs...) = Edge(path, attrs)
Edge(path::Vararg{NodeID}; attrs...) = Edge(collect(path), attrs)
Edge(path::Vector{String}, attrs) = Edge(map(NodeID, path), attrs)
Edge(path::Vector{String}; attrs...) = Edge(map(NodeID, path), attrs)
Edge(path::Vararg{String}; attrs...) = Edge(map(NodeID, collect(path)), attrs)

# Bindings
##########

""" Run a Graphviz program.

Assumes that Graphviz is installed on the local system and invokes Graphviz
through its command-line interface.

For bindings to the Graphviz C API, see the the package
[GraphViz.jl](https://github.com/Keno/GraphViz.jl). At the time of this writing,
GraphViz.jl is unmaintained.
"""
function run_graphviz(io::IO, graph::Graph; prog::String="dot", format::String="json0")
  open(`$prog -T$format`, io, write=true) do gv
    pprint(gv, graph)
  end
end
function run_graphviz(graph::Graph; kw...)
  io = IOBuffer()
  run_graphviz(io, graph; kw...)
  seekstart(io)
end

function Base.show(io::IO, ::MIME"image/svg+xml", graph::Graph)
  run_graphviz(io, graph, format="svg")
end

# MetaGraphs
############

""" Parse Graphviz output in JSON format.

Returns a MetaGraph with graph layout and other metadata. Each node has a
position and size.

All units are in points. Note that Graphviz has 72 points per inch.
"""
function parse_graphviz(doc::AbstractDict;
                        multigraph::Bool=false)::MetaGraphs.AbstractMetaGraph
  graph = doc["directed"] ? MetaGraphs.MetaDiGraph() : MetaGraphs.MetaGraph()
  nsubgraphs = doc["_subgraph_cnt"] # Subgraphs are ignored.
  
  # Graph-level layout: bounds and padding.
  # It seems, but is not documented, that the first two numbers in the Graphviz
  # bounding box are always zero.
  set_props!(graph, Dict(
    :bounds => SVector{2}(parse_vector(doc["bb"])[3:4]),
    :pad => 72*parse_point(get(doc, "pad", "0,0")),
    :rankdir => get(doc, "rankdir", "TB"),
  ))
  
  # Add vertex for each Graphviz node.
  node_keys = ("id", "name", "comment", "label", "shape", "style")
  for node in doc["objects"][nsubgraphs+1:end]
    props = Dict{Symbol,Any}(
      Symbol(k) => node[k] for k in node_keys if haskey(node, k))
    props[:position] = parse_point(node["pos"])
    props[:size] = 72*SVector(
      parse(Float64, node["width"]),
      parse(Float64, node["height"])
    )
    add_vertex!(graph, props)
  end
  
  # Add edge for each Graphviz edge.
  edge_keys = ("id", "comment", "label", "xlabel", "headlabel", "taillabel",
               "headport", "tailport")
  for edge in doc["edges"]
    if get(edge, "style", nothing) == "invis"
      # Omit invisible edges, which are used to tweak the layout in Graphviz.
      continue
    end
    props = Dict{Symbol,Any}(
      Symbol(k) => edge[k] for k in edge_keys if haskey(edge, k))
    props[:spline] = parse_spline(edge["pos"])
    src = edge["tail"] - nsubgraphs + 1
    tgt = edge["head"] - nsubgraphs + 1
    if multigraph
      if add_edge!(graph, src, tgt)
        set_prop!(graph, src, tgt, :edges, [props])
      else
        push!(get_prop(graph, src, tgt, :edges), props)
      end
    else
      @assert add_edge!(graph, src, tgt, props)
    end
  end
  
  graph
end

""" Parse an array of floats in Graphviz's comma-separated format.
"""
parse_vector(s::AbstractString) = [ parse(Float64, x) for x in split(s, ",") ]

""" Parse Graphviz point.

http://www.graphviz.org/doc/info/attrs.html#k:point
"""
parse_point(s::AbstractString) = SVector{2}(parse_vector(s))

""" Parse Graphviz spline.

In Graphviz, a "spline" is a cubic B-spline of overlapping cubic Bezier curves.
It consists of 3n+1 points, where n is the number of Bezier curves.

http://www.graphviz.org/doc/info/attrs.html#k:splineType
https://web.archive.org/web/20170418034924/http://www.graphviz.org/content/how-convert-b-spline-bezier
"""
function parse_spline(spline::AbstractString)
  points = StaticVector{2,Float64}[]
  start, stop = nothing, nothing
  for s in split(spline, " ")
    if startswith(s, "s,"); start = parse_point(s[3:end])
    elseif startswith(s, "e,"); stop = parse_point(s[3:end])
    else push!(points, parse_point(s)) end
  end
  # Prefer explicit start or end points to the spline start and end points.
  # Thus, endpoints may pass into the node shape but should not fall short.
  if !isnothing(start); points[0] = start end
  if !isnothing(stop); points[end] = stop end
  points
end

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
    graph_attrs = as_attributes(get(attrs, :graph, Dict())),
    node_attrs = as_attributes(get(attrs, :node, Dict())),
    edge_attrs = as_attributes(get(attrs, :edge, Dict())),
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
