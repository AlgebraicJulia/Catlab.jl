""" Data structures for graphs, based on C-sets.

Support for graphs, symmetric graphs, and half-edge graphs.
"""
module BasicGraphs
export AbstractGraph, Graph, AbstractSymmetricGraph, SymmetricGraph,
  nv, ne, src, tgt, inv, edges, vertices, has_edge, has_vertex,
  add_edge!, add_edges!, add_vertex!, add_vertices!,
  neighbors, inneighbors, outneighbors, all_neighbors,
  AbstractHalfEdgeGraph, HalfEdgeGraph, vertex, half_edges,
  add_dangling_edge!, add_dangling_edges!

import Base: inv
import LightGraphs: SimpleGraph, SimpleDiGraph, nv, ne, src, dst,
  edges, vertices, has_edge, has_vertex, add_edge!, add_vertex!, add_vertices!,
  neighbors, inneighbors, outneighbors, all_neighbors

using ...Present, ...CSetDataStructures

# Graphs
########

@present TheoryGraph(FreeSchema) begin
  V::Ob
  E::Ob
  src::Hom(E,V)
  tgt::Hom(E,V)
end

const AbstractGraph = AbstractACSetType(TheoryGraph)
const Graph = CSetType(TheoryGraph, index=[:src,:tgt])

function (::Type{T})(nv::Int) where T <: AbstractGraph
  g = T(); add_vertices!(g, nv); g
end

nv(g::AbstractACSet) = nparts(g, :V)
ne(g::AbstractACSet) = nparts(g, :E)
ne(g::AbstractACSet, src::Int, tgt::Int) =
  count(subpart(g, e, :tgt) == tgt for e in incident(g, src, :src))

src(g::AbstractACSet, args...) = subpart(g, args..., :src)
tgt(g::AbstractACSet, args...) = subpart(g, args..., :tgt)
dst(g::AbstractACSet, args...) = tgt(g, args...) # LightGraphs compatibility

vertices(g::AbstractACSet) = 1:nv(g)
edges(g::AbstractACSet) = 1:ne(g)
edges(g::AbstractACSet, src::Int, tgt::Int) =
  (e for e in incident(g, src, :src) if subpart(g, e, :tgt) == tgt)

has_vertex(g::AbstractACSet, v) = has_part(g, :V, v)
has_edge(g::AbstractACSet, e) = has_part(g, :E, e)
has_edge(g::AbstractACSet, src::Int, tgt::Int) = tgt ∈ outneighbors(g, src)

add_vertex!(g::AbstractACSet; kw...) = add_part!(g, :V; kw...)
add_vertices!(g::AbstractACSet, n::Int; kw...) = add_parts!(g, :V, n; kw...)

add_edge!(g::AbstractGraph, src::Int, tgt::Int; kw...) =
  add_part!(g, :E; src=src, tgt=tgt, kw...)

function add_edges!(g::AbstractGraph, srcs::AbstractVector{Int},
                    tgts::AbstractVector{Int}; kw...)
  @assert (n = length(srcs)) == length(tgts)
  add_parts!(g, :E, n; src=srcs, tgt=tgts, kw...)
end

neighbors(g::AbstractGraph, v::Int) = outneighbors(g, v)
inneighbors(g::AbstractGraph, v::Int) = subpart(g, incident(g, v, :tgt), :src)
outneighbors(g::AbstractGraph, v::Int) = subpart(g, incident(g, v, :src), :tgt)
all_neighbors(g::AbstractGraph, v::Int) =
  Iterators.flatten((inneighbors(g, v), outneighbors(g, v)))

# # Symmetric graphs
# ##################

@present TheorySymmetricGraph <: TheoryGraph begin
  inv::Hom(E,E)

  compose(inv,inv) == id(E)
  compose(inv,src) == tgt
  compose(inv,tgt) == src
end

# Don't index `inv` because it is self-inverse and don't index `tgt`
# because `src` contains the same information due to symmetry of graph.
const AbstractSymmetricGraph = AbstractACSetType(TheorySymmetricGraph)
const SymmetricGraph = CSetType(TheorySymmetricGraph, index=[:src])

function (::Type{T})(nv::Int) where T <: AbstractSymmetricGraph
  g = T(); add_vertices!(g, nv); g
end

inv(g::AbstractACSet, args...) = subpart(g, args..., :inv)

add_edge!(g::AbstractSymmetricGraph, src::Int, tgt::Int; kw...) =
  add_edges!(g, src:src, tgt:tgt; kw...)

function add_edges!(g::AbstractSymmetricGraph, srcs::AbstractVector{Int},
                    tgts::AbstractVector{Int}; kw...)
  @assert (n = length(srcs)) == length(tgts)
  k = nparts(g, :E)
  add_parts!(g, :E, 2n; src=vcat(srcs,tgts), tgt=vcat(tgts,srcs),
             inv=vcat((k+n+1):(k+2n),(k+1):(k+n)), kw...)
end

neighbors(g::AbstractSymmetricGraph, v::Int) =
  subpart(g, incident(g, v, :src), :tgt)
inneighbors(g::AbstractSymmetricGraph, v::Int) = neighbors(g, v)
outneighbors(g::AbstractSymmetricGraph, v::Int) = neighbors(g, v)
all_neighbors(g::AbstractSymmetricGraph, v::Int) = neighbors(g, v)

# Half-edge graphs
##################

@present TheoryHalfEdgeGraph(FreeSchema) begin
  V::Ob
  H::Ob
  vertex::Hom(H,V)
  inv::Hom(H,H)

  compose(inv, inv) == id(H)
end

const AbstractHalfEdgeGraph = AbstractACSetType(TheoryHalfEdgeGraph)
const HalfEdgeGraph = CSetType(TheoryHalfEdgeGraph, index=[:vertex])

function (::Type{T})(nv::Int) where T <: AbstractHalfEdgeGraph
  g = T(); add_vertices!(g, nv); g
end

vertex(g::AbstractACSet, args...) = subpart(g, args..., :vertex)

half_edges(g::AbstractACSet) = 1:nparts(g, :H)
half_edges(g::AbstractACSet, v) = incident(g, v, :vertex)

add_edge!(g::AbstractHalfEdgeGraph, src::Int, tgt::Int; kw...) =
  add_edges!(g, src:src, tgt:tgt; kw...)

function add_edges!(g::AbstractHalfEdgeGraph, srcs::AbstractVector{Int},
                    tgts::AbstractVector{Int}; kw...)
  @assert (n = length(srcs)) == length(tgts)
  k = nparts(g, :H)
  add_parts!(g, :H, 2n; vertex=vcat(srcs,tgts),
             inv=vcat((k+n+1):(k+2n),(k+1):(k+n)), kw...)
end

add_dangling_edge!(g::AbstractHalfEdgeGraph, v::Int; kw...) =
  add_part!(g, :H; vertex=v, inv=nparts(g,:H)+1)

function add_dangling_edges!(g::AbstractHalfEdgeGraph,
                             vs::AbstractVector{Int}; kw...)
  n, k = length(vs), nparts(g, :H)
  add_parts!(g, :H, n; vertex=vs, inv=(k+1):(k+n), kw...)
end

# LightGraphs constructors
##########################

function (::Type{LG})(g::Union{AbstractGraph,AbstractSymmetricGraph}) where
    LG <: Union{SimpleGraph,SimpleDiGraph}
  lg = LG(nv(g))
  for e in edges(g)
    add_edge!(lg, src(g,e), tgt(g,e))
  end
  lg
end

function SimpleGraph(g::AbstractHalfEdgeGraph)
  lg = SimpleGraph(nv(g))
  for e in half_edges(g)
    e′ = inv(g,e)
    if e <= e′
      add_edge!(lg, vertex(g,e), vertex(g,e′))
    end
  end
  lg
end

end
