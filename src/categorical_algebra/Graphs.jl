""" Data structures for graphs, based on C-sets.

Support for graphs, symmetric graphs, and property graphs.
"""
module Graphs
export AbstractGraph, Graph, AbstractSymmetricGraph, SymmetricGraph,
  nv, ne, src, dst, edges, has_edge, has_vertex,
  add_edge!, add_edges!, add_vertex!, add_vertices!,
  neighbors, inneighbors, outneighbors, all_neighbors,
  PropertyGraph, gprops, vprops, eprops, get_gprop, get_vprop, get_eprop,
  set_gprop!, set_vprop!, set_eprop!

import LightGraphs
import LightGraphs: nv, ne, src, dst, edges, has_edge, has_vertex,
  add_edge!, add_vertex!, add_vertices!,
  neighbors, inneighbors, outneighbors, all_neighbors

using ...Present
using ...Theories: Category, FreeCategory, dom, codom, compose, id
using ..CSets

# Graphs
########

@present TheoryGraph(FreeCategory) begin
  V::Ob
  E::Ob
  src::Hom(E,V)
  tgt::Hom(E,V)
end

const Graph = CSetType(TheoryGraph, index=[:src,:tgt])
const AbstractGraph = supertype(Graph)

nv(g::AbstractGraph) = nparts(g, :V)
ne(g::AbstractGraph) = nparts(g, :E)
ne(g::AbstractGraph, src::Int, tgt::Int) =
  count(subpart(g, e, :tgt) == tgt for e in incident(g, src, :src))

src(g::AbstractGraph, e) = subpart(g, e, :src)
dst(g::AbstractGraph, e) = subpart(g, e, :tgt)
edges(g::AbstractGraph) = 1:ne(g)
edges(g::AbstractGraph, src::Int, tgt::Int) =
  (e for e in incident(g, src, :src) if subpart(g, e, :tgt) == tgt)

has_vertex(g::AbstractGraph, v::Int) = 1 <= v <= nv(g)
has_edge(g::AbstractGraph, e::Int) = 1 <= e <= ne(g)
has_edge(g::AbstractGraph, src::Int, tgt::Int) = tgt ∈ outneighbors(g, src)

add_vertex!(g::AbstractGraph) = add_part!(g, :V)
add_vertices!(g::AbstractGraph, n::Int) = add_parts!(g, :V, n)

add_edge!(g::AbstractGraph, src::Int, tgt::Int) =
  add_part!(g, :E, (src=src, tgt=tgt))

function add_edges!(g::AbstractGraph, srcs::AbstractVector{Int},
                    tgts::AbstractVector{Int})
  @assert length(srcs) == length(tgts)
  add_parts!(g, :E, length(srcs), (src=srcs, tgt=tgts))
end

neighbors(g::AbstractGraph, v::Int) = outneighbors(g, v)
inneighbors(g::AbstractGraph, v::Int) = subpart(g, incident(g, v, :tgt), :src)
outneighbors(g::AbstractGraph, v::Int) = subpart(g, incident(g, v, :src), :tgt)
all_neighbors(g::AbstractGraph, v::Int) =
  Iterators.flatten((inneighbors(g, v), outneighbors(g, v)))

# Symmetric graphs
##################

@present TheorySymmetricGraph(FreeCategory) begin
  V::Ob
  E::Ob
  src::Hom(E,V)
  tgt::Hom(E,V)
  inv::Hom(E,E)

  compose(inv,inv) == id(E)
  compose(inv,src) == tgt
  compose(inv,tgt) == src
end

# Don't index `inv` because it is self-inverse and don't index `tgt`
# because `src` contains the same information due to symmetry of graph.
const SymmetricGraph = CSetType(TheorySymmetricGraph, index=[:src])
const AbstractSymmetricGraph = supertype(SymmetricGraph)

# In implementing the LightGraphs API, regard edge pairs as a single edge.
nv(g::AbstractSymmetricGraph) = nparts(g, :V)
ne(g::AbstractSymmetricGraph) = nparts(g, :E) ÷ 2
ne(g::AbstractSymmetricGraph, src::Int, tgt::Int) =
  count(subpart(g, e, :tgt) == tgt for e in incident(g, src, :src))

src(g::AbstractSymmetricGraph, e) = subpart(g, e, :src)
dst(g::AbstractSymmetricGraph, e) = subpart(g, e, :tgt)
edges(g::AbstractSymmetricGraph) = 1:nparts(g, :E)
edges(g::AbstractSymmetricGraph, src::Int, tgt::Int) =
  (e for e in incident(g, src, :src) if subpart(g, e, :tgt) == tgt)

has_vertex(g::AbstractSymmetricGraph, v::Int) = 1 <= v <= nparts(g, :V)
has_edge(g::AbstractSymmetricGraph, e::Int) = 1 <= e <= nparts(g, :E)
has_edge(g::AbstractSymmetricGraph, src::Int, tgt::Int) = tgt ∈ neighbors(g, src)

add_vertex!(g::AbstractSymmetricGraph) = add_part!(g, :V)
add_vertices!(g::AbstractSymmetricGraph, n::Int) = add_parts!(g, :V, n)

add_edge!(g::AbstractSymmetricGraph, src::Int, tgt::Int) =
  add_edges!(g, src:src, tgt:tgt)

function add_edges!(g::AbstractSymmetricGraph, srcs::AbstractVector{Int},
                    tgts::AbstractVector{Int})
  n = length(srcs)
  @assert length(tgts) == n
  invs = nparts(g, :E) .+ [(n+1):2n; 1:n]
  add_parts!(g, :E, 2n, (src=[srcs; tgts], tgt=[tgts; srcs], inv=invs))
end

neighbors(g::AbstractSymmetricGraph, v::Int) =
  subpart(g, incident(g, v, :src), :tgt)
inneighbors(g::AbstractSymmetricGraph, v::Int) = neighbors(g, v)
outneighbors(g::AbstractSymmetricGraph, v::Int) = neighbors(g, v)
all_neighbors(g::AbstractSymmetricGraph, v::Int) = neighbors(g, v)

# Property graphs
#################

@present TheoryPropertyGraph(FreeCategory) begin
  V::Ob
  E::Ob
  Props::Ob
  src::Hom(E,V)
  tgt::Hom(E,V)
  vprops::Hom(V,Props)
  eprops::Hom(E,Props)
end

# By default, don't index `:src` or `:tgt` since generic property graphs are
# often just data storage.
const _PropertyGraph = CSetType(TheoryPropertyGraph, data=[:Props], index=[])
const _AbstractPropertyGraph = supertype(_PropertyGraph)

""" Graph with properties.

"Property graphs" are graphs with arbitrary named properties on the graph,
vertices, and edges. They are intended for applications with a large number of
ad-hoc properties. If you have a small number of known properties, it is better
and more efficient to create a specialized C-set type using [`CSetType`](@ref).
"""
struct PropertyGraph{T,G<:_AbstractPropertyGraph}
  graph::G
  gprops::Dict{Symbol,T}
end

function PropertyGraph{T,G}() where {T,G<:_AbstractPropertyGraph}
  graph = G(vprops=Dict{Symbol,T}, eprops=Dict{Symbol,T})
  PropertyGraph{T,G}(graph, Dict{Symbol,T}())
end
PropertyGraph{T}() where T = PropertyGraph{T,_PropertyGraph}()

@inline gprops(g::PropertyGraph) = g.gprops
@inline vprops(g::PropertyGraph, v::Int) = subpart(g.graph, v, :vprops)
@inline eprops(g::PropertyGraph, e::Int) = subpart(g.graph, e, :eprops)

get_gprop(g::PropertyGraph, key::Symbol) = gprops(g)[key]
get_vprop(g::PropertyGraph, v::Int, key::Symbol) = vprops(g,v)[key]
get_eprop(g::PropertyGraph, e::Int, key::Symbol) = eprops(g,e)[key]

set_gprop!(g::PropertyGraph, key::Symbol, value) = (gprops(g)[key] = value)
set_vprop!(g::PropertyGraph, v::Int, key::Symbol, value) =
  (vprops(g,v)[key] = value)
set_eprop!(g::PropertyGraph, e::Int, key::Symbol, value) =
  (eprops(g,e)[key] = value)

nv(g::PropertyGraph) = nparts(g.graph, :V)
ne(g::PropertyGraph) = nparts(g.graph, :E)

src(g::PropertyGraph, e) = subpart(g.graph, e, :src)
dst(g::PropertyGraph, e) = subpart(g.graph, e, :tgt)
edges(g::PropertyGraph) = 1:ne(g)

has_vertex(g::PropertyGraph, v::Int) = 1 <= v <= nv(g)
has_edge(g::PropertyGraph, e::Int) = 1 <= v <= ne(g)

add_vertex!(g::PropertyGraph{T}; kw...) where T =
  add_vertex!(g, Dict{Symbol,T}(kw...))
add_vertex!(g::PropertyGraph{T}, d::Dict{Symbol,T}) where T =
  add_part!(g.graph, :V, (vprops=d,))

add_vertices!(g::PropertyGraph{T}, n::Int) where T =
  add_parts!(g.graph, :V, n, (vprops=(Dict{Symbol,T}() for i=1:n),))

add_edge!(g::PropertyGraph{T}, src::Int, tgt::Int; kw...) where T =
  add_edge!(g, src, tgt, Dict{Symbol,T}(kw...))
add_edge!(g::PropertyGraph{T}, src::Int, tgt::Int, d::Dict{Symbol,T}) where T =
  add_part!(g.graph, :E, (src=src, tgt=tgt, eprops=d))

function add_edges!(g::PropertyGraph{T}, srcs::AbstractVector{Int},
                    tgts::AbstractVector{Int}) where T
  n = length(srcs)
  @assert length(tgts) == n
  eprops = (Dict{Symbol,T}() for i=1:n)
  add_parts!(g.graph, :E, n, (src=srcs, tgt=tgts, eprops=eprops))
end

# LightGraphs interop
#####################

function LightGraphs.SimpleDiGraph(
    g::Union{AbstractGraph,AbstractSymmetricGraph})
  lg = LightGraphs.SimpleDiGraph(nv(g))
  for e in edges(g); add_edge!(lg, src(g,e), dst(g,e)) end
  lg
end

function LightGraphs.SimpleGraph(
    g::Union{AbstractGraph,AbstractSymmetricGraph})
  lg = LightGraphs.SimpleGraph(nv(g))
  for e in edges(g); add_edge!(lg, src(g,e), dst(g,e)) end
  lg
end

end
