""" Bipartite graphs, directed and undirected, as C-sets.

A graph theorist might call these "bipartitioned graphs," as in a graph
*equipped with* a bipartition, as opposed to "bipartite graphs," as in a graph
that *can be* bipartitioned. Here we use the former notion, which is more
natural from the structuralist perspective, but the latter terminology, which is
shorter and more familiar.
"""
module BipartiteGraphs
export AbstractUndirectedBipartiteGraph, UndirectedBipartiteGraph,
  AbstractBipartiteGraph, BipartiteGraph, nv₁, nv₂, vertices₁, vertices₂,
  ne₁₂, ne₂₁, edges₁₂, edges₂₁, src₁, src₂, tgt₁, tgt₂,
  add_vertex₁!, add_vertex₂!, add_vertices₁!, add_vertices₂!,
  rem_vertex₁!, rem_vertex₂!, rem_vertices₁!, rem_vertices₂!,
  add_edge₁₂!, add_edge₂₁!, add_edges₁₂!, add_edges₂₁!,
  rem_edge₁₂!, rem_edge₂₁!, rem_edges₁₂!, rem_edges₂₁!

using ...Present, ...CSetDataStructures
using ..BasicGraphs: flatten
import ..BasicGraphs: nv, ne, vertices, edges, inneighbors, outneighbors

# Undirected bipartite graphs
#############################

@present TheoryUndirectedBipartiteGraph(FreeSchema) begin
  (V₁, V₂)::Ob
  E::Ob
  src::Hom(E, V₁)
  tgt::Hom(E, V₂)
end

""" Abstract type for undirected bipartite graphs.
"""
const AbstractUndirectedBipartiteGraph =
  AbstractACSetType(TheoryUndirectedBipartiteGraph)

""" An undirected bipartite graph.

It is a matter of perspective whether to consider such graphs "undirected," in
the sense that the edges have no orientation, or "unidirected," in the sense
that all edges go from vertices of type 1 to vertices of type 2.
"""
const UndirectedBipartiteGraph =
  CSetType(TheoryUndirectedBipartiteGraph, index=[:src, :tgt])

""" Number of vertices of type 1 in a bipartite graph.
"""
nv₁(g::AbstractACSet) = nparts(g, :V₁)

""" Number of vertices of type 2 in a bipartite graph.
"""
nv₂(g::AbstractACSet) = nparts(g, :V₂)

""" Vertices of type 1 in a bipartite graph.
"""
vertices₁(g::AbstractACSet) = parts(g, :V₁)

""" Vertices of type 2 in a bipartite graph.
"""
vertices₂(g::AbstractACSet) = parts(g, :V₂)

""" Add a vertex of type 1 to a bipartite graph.
"""
add_vertex₁!(g::AbstractACSet; kw...) = add_part!(g, :V₁; kw...)

""" Add a vertex of type 2 to a bipartite graph.
"""
add_vertex₂!(g::AbstractACSet; kw...) = add_part!(g, :V₂; kw...)

""" Add vertices of type 1 to a bipartite graph.
"""
add_vertices₁!(g::AbstractACSet, n::Int; kw...) = add_parts!(g, :V₁, n; kw...)

""" Add vertices of type 2 to a bipartite graph.
"""
add_vertices₂!(g::AbstractACSet, n::Int; kw...) = add_parts!(g, :V₂, n; kw...)

""" Remove vertex of type 1 from a bipartite graph.
"""
rem_vertex₁!(g::AbstractACSet, v::Int; kw...) = rem_vertices₁!(g, v:v; kw...)

""" Remove vertex of type 2 from a bipartite graph.
"""
rem_vertex₂!(g::AbstractACSet, v::Int; kw...) = rem_vertices₂!(g, v:v; kw...)

""" Remove vertices of type 1 from a bipartite graph.
"""
function rem_vertices₁!(g::AbstractUndirectedBipartiteGraph, vs;
                        keep_edges::Bool=false)
  if !keep_edges
    rem_parts!(g, :E, unique!(sort!(flatten(incident(g, vs, :src)))))
  end
  rem_parts!(g, :V₁, vs)
end

""" Remove vertices of type 2 from a bipartite graph.
"""
function rem_vertices₂!(g::AbstractUndirectedBipartiteGraph, vs;
                        keep_edges::Bool=false)
  if !keep_edges
    rem_parts!(g, :E, unique!(sort!(flatten(incident(g, vs, :tgt)))))
  end
  rem_parts!(g, :V₂, vs)
end

inneighbors(g::AbstractUndirectedBipartiteGraph, v::Int) =
  subpart(g, incident(g, v, :tgt), :src)
outneighbors(g::AbstractUndirectedBipartiteGraph, v::Int) =
  subpart(g, incident(g, v, :src), :tgt)

# Bipartite graphs
##################

@present TheoryBipartiteGraph(FreeSchema) begin
  (V₁, V₂)::Ob
  (E₁₂, E₂₁)::Ob
  src₁::Hom(E₁₂, V₁)
  tgt₂::Hom(E₁₂, V₂)
  src₂::Hom(E₂₁, V₂)
  tgt₁::Hom(E₂₁, V₁)
end

""" Abstract type for bipartite graphs.
"""
const AbstractBipartiteGraph = AbstractACSetType(TheoryBipartiteGraph)

""" A bipartite graph, better known as a [bipartite directed
multigraph](https://cs.stackexchange.com/a/91521).

Such graphs are isomorphic to port hypergraphs.
"""
const BipartiteGraph = CSetType(TheoryBipartiteGraph,
                                index=[:src₁, :src₂, :tgt₁, :tgt₂])

const AnyBipartiteGraph =
  Union{AbstractBipartiteGraph,AbstractUndirectedBipartiteGraph}

function (::Type{T})(nv₁::Int, nv₂::Int) where T <: AnyBipartiteGraph
  g = T()
  add_parts!(g, :V₁, nv₁)
  add_parts!(g, :V₂, nv₂)
  return g
end

nv(g::AnyBipartiteGraph) = (nv₁(g), nv₂(g))
vertices(g::AnyBipartiteGraph) = (vertices₁(g), vertices₂(g))

ne(g::AbstractBipartiteGraph) = (ne₁₂(g), ne₂₁(g))
edges(g::AbstractBipartiteGraph) = (edges₁₂(g), edges₂₁(g))

""" Number of edges from V₁ to V₂ in a bipartite graph.
"""
ne₁₂(g::AbstractACSet) = nparts(g, :E₁₂)
ne₁₂(g::AbstractACSet, src::Int, tgt::Int) =
  count(subpart(g, e, :tgt₂) == tgt for e in incident(g, src, :src₁))

""" Number of edges from V₂ to V₁ in a bipartite graph.
"""
ne₂₁(g::AbstractACSet) = nparts(g, :E₂₁)
ne₂₁(g::AbstractACSet, src::Int, tgt::Int) =
  count(subpart(g, e, :tgt₁) == tgt for e in incident(g, src, :src₂))

""" Edges from V₁ to V₂ in a bipartite graph.
"""
edges₁₂(g::AbstractACSet) = parts(g, :E₁₂)
edges₁₂(g::AbstractACSet, src::Int, tgt::Int) =
  (e for e in incident(g, src, :src₁) if subpart(g, e, :tgt₂) == tgt)

""" Edges from V₂ to V₁ in a bipartite graph.
"""
edges₂₁(g::AbstractACSet) = parts(g, :E₂₁)
edges₂₁(g::AbstractACSet, src::Int, tgt::Int) =
  (e for e in incident(g, src, :src₂) if subpart(g, e, :tgt₁) == tgt)

""" Source vertex of edge from V₁ to V₂ in a bipartite graph.
"""
src₁(g::AbstractACSet, args...) = subpart(g, args..., :src₁)

""" Target vertex of edge from V₁ to V₂ in a bipartite graph.
"""
tgt₂(g::AbstractACSet, args...) = subpart(g, args..., :tgt₂)

""" Source vertex of edge from V₂ to V₁ in a bipartite graph.
"""
src₂(g::AbstractACSet, args...) = subpart(g, args..., :src₂)

""" Target vertex of edge from V₂ to V₁ in a bipartite graph.
"""
tgt₁(g::AbstractACSet, args...) = subpart(g, args..., :tgt₁)

""" Add edge from V₁ to V₂ in a bipartite graph.
"""
add_edge₁₂!(g::AbstractACSet, src::Int, tgt::Int; kw...) =
  add_part!(g, :E₁₂; src₁=src, tgt₂=tgt, kw...)

""" Add edge from V₂ to V₁ in a bipartite graph.
"""
add_edge₂₁!(g::AbstractACSet, src::Int, tgt::Int; kw...) =
  add_part!(g, :E₂₁; src₂=src, tgt₁=tgt, kw...)

""" Add edges from V₁ to V₂ in a bipartite graph.
"""
function add_edges₁₂!(g::AbstractACSet, srcs::AbstractVector{Int},
                      tgts::AbstractVector{Int}; kw...)
  @assert (n = length(srcs)) == length(tgts)
  add_parts!(g, :E₁₂, n; src₁=srcs, tgt₂=tgts, kw...)
end

""" Add edges from V₂ to V₁ in a bipartite graph.
"""
function add_edges₂₁!(g::AbstractACSet, srcs::AbstractVector{Int},
                      tgts::AbstractVector{Int}; kw...)
  @assert (n = length(srcs)) == length(tgts)
  add_parts!(g, :E₂₁, n; src₂=srcs, tgt₁=tgts, kw...)
end

function rem_vertices₁!(g::AbstractBipartiteGraph, vs; keep_edges::Bool=false)
  if !keep_edges
    rem_parts!(g, :E₁₂, unique!(sort!(flatten(incident(g, vs, :src₁)))))
    rem_parts!(g, :E₂₁, unique!(sort!(flatten(incident(g, vs, :tgt₁)))))
  end
  rem_parts!(g, :V₁, vs)
end

function rem_vertices₂!(g::AbstractBipartiteGraph, vs; keep_edges::Bool=false)
  if !keep_edges
    rem_parts!(g, :E₂₁, unique!(sort!(flatten(incident(g, vs, :src₂)))))
    rem_parts!(g, :E₁₂, unique!(sort!(flatten(incident(g, vs, :tgt₂)))))
  end
  rem_parts!(g, :V₂, vs)
end

""" Remove edge from V₁ to V₂ in a bipartite graph.
"""
rem_edge₁₂!(g::AbstractBipartiteGraph, e::Int) = rem_part!(g, :E₁₂, e)
rem_edge₁₂!(g::AbstractBipartiteGraph, src::Int, tgt::Int) =
  rem_edge₁₂!(g, first(edges₁₂(g, src, tgt)))

""" Remove edge from V₁ to V₂ in a bipartite graph.
"""
rem_edge₂₁!(g::AbstractBipartiteGraph, e::Int) = rem_part!(g, :E₂₁, e)
rem_edge₂₁!(g::AbstractBipartiteGraph, src::Int, tgt::Int) =
  rem_edge₂₁!(g, first(edges₂₁(g, src, tgt)))

""" Remove edges from V₁ to V₂ in a bipartite graph.
"""
rem_edges₁₂!(g::AbstractBipartiteGraph, es) = rem_parts!(g, :E₁₂, es)

""" Remove edges from V₂ to V₁ in a bipartite graph.
"""
rem_edges₂₁!(g::AbstractBipartiteGraph, es) = rem_parts!(g, :E₂₁, es)

end
