module GraphGenerators
export path_graph, cycle_graph, complete_graph, star_graph, wheel_graph,
  parallel_arrows

using ...CSetDataStructures, ..BasicGraphs
using ...CSetDataStructures: hom

""" Path graph on ``n`` vertices.
"""
function path_graph(::Type{T}, n::Int; V=(;), E=(;)) where T <: ACSet
  g = T()
  add_vertices!(g, n; V...)
  add_edges!(g, 1:(n-1), 2:n; E...)
  g
end

""" Cycle graph on ``n`` vertices.

When ``n = 1``, this is a loop graph.
"""
function cycle_graph(::Type{T}, n::Int; V=(;), E=(;)) where T <: ACSet
  g = T()
  add_vertices!(g, n; V...)
  add_edges!(g, 1:n, circshift(1:n, -1); E...)
  g
end

""" Complete graph on ``n`` vertices.
"""
function complete_graph(::Type{T}, n::Int; V=(;)) where T <: ACSet
  g = T()
  add_vertices!(g, n; V...)
  for i in vertices(g), j in vertices(g)
    if i != j && (is_directed(T) || i < j)
      add_edge!(g, i, j)
    end
  end
  g
end

""" Star graph on ``n`` vertices.

In the directed case, the edges point outward.
"""
function star_graph(::Type{T}, n::Int) where T <: ACSet
  g = T()
  add_vertices!(g, n)
  add_edges!(g, fill(n,n-1), 1:(n-1))
  g
end

""" Wheel graph on ``n`` vertices.

In the directed case, the outer cycle is directed and the spokes point outward.
"""
function wheel_graph(::Type{T}, n::Int) where T <: ACSet
  g = cycle_graph(T, n-1)
  add_vertex!(g)
  add_edges!(g, fill(n,n-1), 1:(n-1))
  g
end

""" Graph with two vertices and ``n`` parallel edges.
"""
function parallel_arrows(::Type{T}, n::Int; V=(;), E=(;)) where T <: ACSet
  g = T()
  add_vertices!(g, 2; V...)
  add_edges!(g, fill(1,n), fill(2,n); E...)
  g
end

# Should this be exported from `BasicGraphs`?
@generated is_directed(::Type{T}) where {S, T<:StructACSet{S}} = :inv ∉ hom(S)

end
