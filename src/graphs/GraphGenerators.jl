module GraphGenerators
export path_graph, cycle_graph

using ...CSetDataStructures, ..BasicGraphs

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

end
