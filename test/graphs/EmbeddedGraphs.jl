module TestEmbeddedGraphs
using Test

using Catlab.Graphs.BasicGraphs, Catlab.Graphs.EmbeddedGraphs

# Rotation graphs
#################

""" Wheel graph on `n` vertices with its unique planar embedding.
"""
function embedded_wheel_graph(n::Int)
  @assert n >= 4
  n = n - 1 # Count using number of outer vertices.
  g = RotationGraph()
  for i in 1:n # Outer corollas.
    add_corolla!(g, 3)
  end
  add_corolla!(g, n) # Inner corolla.
  pair_half_edges!(g, (3n+1):4n, 2:3:3n) # inner <-> outer
  pair_half_edges!(g, 1:3:3n, circshift(3:3:3n, -1)) # outer <-> outer
  g
end

g = embedded_wheel_graph(5)
@test nv(g) == 5
@test length(half_edges(g)) == 16

@test half_edges(g, 1) == [1,2,3]
@test half_edges(g, 5) == [13,14,15,16]
@test σ(g, [1,2,3]) == [2,3,1]
@test σ(g, [13,14,15,16]) == [14,15,16,13]

end
