""" A directed multigraph with "ports".

Graphs whose vertices have "ports" occur frequently in software engineering
practice, but don't seem to have a standard
[terminology](https://cs.stackexchange.com/q/41320) in mathematics or
theoretical CS. In the graph rewriting community, they are called "port graphs".

This module implements a graph data structure that is richer (and "heavier")
than in the existing Julia graph libraries (`Graphs.jl` and `LightGraphs.jl`).
Besides ports, it supports arbitrary key/value properties on vertices, edges,
and graphs. It also supports nested graphs: vertices which are themselves port
graphs.
"""
module PortGraphs
export PortGraph, PortEdge
import DataStructures: OrderedDict, OrderedSet

# Data types
############

typealias AttributeDict OrderedDict{Symbol,Any}

# XXX: `BaseEdge` type and `Vertex` type parameter work around lack of support
# for circular type definitions in Julia:
# https://github.com/JuliaLang/julia/issues/269
type BaseEdge{Vertex}
  source::Vertex # PortGraph
  source_port::Int
  target::Vertex # PortGraph
  target_port::Int
  attributes::AttributeDict
end

""" A port graph (or vertex therein).

In this implementation, vertices and graphs are identified. This convention
enables port graphs to be nested within each other.

The underlying representation is an adjacency list. Specifically, we use a
dict-of-dict-of-set representation, similar but not identical to NetworkX, where
the outer dict contains adjacency lists keyed by vertex, the inner dicts are
adjacency lists keyed by neighbor, and each innermost set contains all the edges
between a given node and neighbor.
"""
type PortGraph{Port,Label}
  label::Label
  ports::Vector{Port}
  succ::OrderedDict{PortGraph,OrderedDict{PortGraph,OrderedSet{Edge{PortGraph}}}}
  pred::OrderedDict{PortGraph,OrderedDict{PortGraph,OrderedSet{Edge{PortGraph}}}}
  attributes::AttributeDict
end

""" An edge in a port graph.
"""
typealias PortEdge Edge{PortGraph}

function PortEdge(src::PortGraph, tgt::PortGraph; kw...)
  PortEdge(src, 0, tgt, 0, OrderedDict(kw))
end
function PortEdge(src::PortGraph, src_port::Int,
                  tgt::PortGraph, tgt_port::Int; kw...)
  PortEdge(src, src_port, tgt, tgt_port, OrderedDict(kw))
end

# Methods
#########

# Accessors
source(PortEdge::e) = e.source
target(PortEdge::e) = e.target
source_port(PortEdge::e) = e.source_port
target_port(PortEdge::e) = e.target_port

function has_vertex(g::PortGraph, v::PortGraph)::Bool
  haskey(g.succ, v) # == haskey(g.pred, v)
end
Base::in(v::PortGraph, g::PortGraph) = has_vertex(g, v)

function has_edge(g::PortGraph, u::PortGraph, v::PortGraph)
  haskey(g.succ, u) && haskey(g.succ[u], v)
  # == haskey(g.pred, v) && haskey(g.pred[v], u)
end

# Mutation

function add_vertex!(g::PortGraph, v::PortGraph)
  if !(v in g)
    g.succ[v] = OrdereDict{PortGraph,OrderedSet{PortEdge}}()
    g.pred[v] = OrdereDict{PortGraph,OrderedSet{PortEdge}}()
  end
  return v
end

function remove_vertex!(g::PortGraph, v)
  for tgt in keys(g.succ[v])
    delete!(g.pred[tgt], v)
  end
  delete!(g.succ, v)
  for src in keys(g.pred[v])
    delete!(g.succ[src], v)
  end
  delete!(g.pred, v)
end

function add_edge!(g::PortGraph, e::PortEdge)
  src, tgt = source(e), target(e)
  add_vertex!(g, src)
  add_vertex!(g, tgt)
  push!(get!(g.succ[src], tgt) do OrderedSet{PortEdge}() end, e)
  push!(get!(g.pred[tgt], src) do OrderedSet{PortEdge}() end, e)
  return e
end

function remove_edge!(g::PortGraph, src::PortGraph, tgt::PortGraph)
  delete!(g.succ[src], tgt)
  delete!(g.pred[tgt], src)
end
function remove_edge!(g::PortGraph, e::PortEdge)
  src, tgt = source(e), target(e)
  delete!(g.succ[src][tgt], e)
  delete!(g.pred[tgt][src], e)
  if isempty(g.succ[src][tgt])
    delete!(g.succ[src], tgt)
    delete!(g.pred[tgt], src)
  end
end
