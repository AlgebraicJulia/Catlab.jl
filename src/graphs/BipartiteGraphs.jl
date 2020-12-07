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
  ne₁₂, ne₂₁, edges₁₂, edges₂₁, src₁, src₂, tgt₁, tgt₂

using ...Present, ...CSetDataStructures

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
the sense that the edges have no orientation at all, or "unidirected," in the
sense that all edges go from vertices of type 1 to vertices of type 2.
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

function (::Type{T})(nv₁::Int, nv₂::Int) where
    {T <: Union{AbstractBipartiteGraph,AbstractUndirectedBipartiteGraph}}
  g = T()
  add_parts!(g, :V₁, nv₁)
  add_parts!(g, :V₂, nv₂)
  return g
end

""" Number of edges from V₁ to V₂ in a bipartite graph.
"""
ne₁₂(g::AbstractACSet) = nparts(g, :E₁₂)

""" Number of edges from V₂ to V₁ in a bipartite graph.
"""
ne₂₁(g::AbstractACSet) = nparts(g, :E₂₁)

""" Edges from V₁ to V₂ in a bipartite graph.
"""
edges₁₂(g::AbstractACSet) = parts(g, :E₁₂)

""" Edges from V₂ to V₁ in a bipartite graph.
"""
edges₂₁(g::AbstractACSet) = parts(g, :E₂₁)

""" Source vertex of edge from V₁ to V₂ in bipartite graph.
"""
src₁(g::AbstractACSet, args...) = subpart(g, args..., :src₁)

""" Target vertex of edge from V₁ to V₂ in bipartite graph.
"""
tgt₂(g::AbstractACSet, args...) = subpart(g, args..., :tgt₂)

""" Source vertex of edge from V₂ to V₁ in bipartite graph.
"""
src₂(g::AbstractACSet, args...) = subpart(g, args..., :src₂)

""" Target vertex of edge from V₂ to V₁ in bipartite graph.
"""
tgt₁(g::AbstractACSet, args...) = subpart(g, args..., :tgt₁)

end
