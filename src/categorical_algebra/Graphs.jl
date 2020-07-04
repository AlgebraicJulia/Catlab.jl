""" Graphs and symmetric graphs as C-sets.
"""
module Graphs
export AbstractGraph, AbstractSymmetricGraph, Graph, SymmetricGraph,
  nv, ne, edges, has_edge, has_vertex, add_edge!, add_vertex!, add_vertices!,
  neighbors, inneighbors, outneighbors, all_neighbors

import LightGraphs
import LightGraphs: nv, ne, edges, has_edge, has_vertex, add_edge!, add_vertex!,
  add_vertices!, neighbors, inneighbors, outneighbors, all_neighbors

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

neighbors(g::AbstractGraph, v::Int) = outneighbors(g, v)
inneighbors(g::AbstractGraph, v::Int) = subpart(g, incident(g, v, :tgt), :src)
outneighbors(g::AbstractGraph, v::Int) = subpart(g, incident(g, v, :src), :tgt)
all_neighbors(g::AbstractGraph, v::Int) =
  Iterators.flatten((inneighbors(g, v), outneighbors(g, v)))

function LightGraphs.SimpleDiGraph(g::AbstractGraph)
  lg = LightGraphs.SimpleDiGraph(nv(g))
  for e in edges(g)
    add_edge!(lg, subpart(g, e, :src), subpart(g, e, :tgt))
  end
  lg
end

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

edges(g::AbstractSymmetricGraph) = 1:nparts(g, :E)
edges(g::AbstractSymmetricGraph, src::Int, tgt::Int) =
  (e for e in incident(g, src, :src) if subpart(g, e, :tgt) == tgt)

has_vertex(g::AbstractSymmetricGraph, v::Int) = 1 <= v <= nparts(g, :V)
has_edge(g::AbstractSymmetricGraph, e::Int) = 1 <= e <= nparts(g, :E)
has_edge(g::AbstractSymmetricGraph, src::Int, tgt::Int) = tgt ∈ neighbors(g, src)

add_vertex!(g::AbstractSymmetricGraph) = add_part!(g, :V)
add_vertices!(g::AbstractSymmetricGraph, n::Int) = add_parts!(g, :V, n)

function add_edge!(g::AbstractSymmetricGraph, src::Int, tgt::Int)
  e1 = nparts(g, :E) + 1
  e2 = e1 + 1
  add_part!(g, :E, (src=src, tgt=tgt, inv=e2))
  add_part!(g, :E, (src=tgt, tgt=src, inv=e1))
  (e1, e2)
end

neighbors(g::AbstractSymmetricGraph, v::Int) =
  subpart(g, incident(g, v, :src), :tgt)
inneighbors(g::AbstractSymmetricGraph, v::Int) = neighbors(g, v)
outneighbors(g::AbstractSymmetricGraph, v::Int) = neighbors(g, v)
all_neighbors(g::AbstractSymmetricGraph, v::Int) = neighbors(g, v)

function LightGraphs.SimpleGraph(g::AbstractSymmetricGraph)
  lg = LightGraphs.SimpleGraph(nv(g))
  for e in edges(g)
    add_edge!(lg, subpart(g, e, :src), subpart(g, e, :tgt))
  end
  lg
end

end
