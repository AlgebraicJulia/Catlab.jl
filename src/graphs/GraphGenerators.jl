module GraphGenerators
export path_graph, cycle_graph, complete_graph, star_graph

using ...CSetDataStructures, ..BasicGraphs
using ...CSetDataStructures: hom

""" Path graph on ``n`` vertices.
"""
function path_graph(::Type{T}, n::Int; V=(;), E=(;)) where T <: AbstractACSet
  g = T()
  add_vertices!(g, n; V...)
  add_edges!(g, 1:(n-1), 2:n; E...)
  g
end

""" Cycle graph on ``n`` vertices.

When ``n = 1``, this is a loop graph.
"""
function cycle_graph(::Type{T}, n::Int; V=(;), E=(;)) where T <: AbstractACSet
  g = T()
  add_vertices!(g, n; V...)
  add_edges!(g, 1:n, circshift(1:n, -1); E...)
  g
end

""" Complete graph on ``n`` vertices.
"""
function complete_graph(::Type{T}, n::Int; V=(;)) where T <: AbstractACSet
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
"""
function star_graph(::Type{T}, n::Int) where T <: AbstractACSet
  g = T()
  add_vertices!(g, n)
  add_edges!(g, fill(n,n-1), 1:(n-1))
  g
end

# Should this be exported from `BasicGraphs`?
@generated is_directed(::Type{T}) where {CD, T<:AbstractACSet{CD}} =
  !(:inv in hom(CD))

end
