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
  pair_half_edges!(g, (3n+1):4n, reverse(2:3:3n)) # Inner <-> outer pairs.
  pair_half_edges!(g, 3:3:3n, circshift(1:3:3n, -1)) # Outer <-> outer pairs.
  g
end

g = embedded_wheel_graph(5)
@test nv(g) == 5
@test length(half_edges(g)) == 16
@test half_edges(g, 1) == [1,2,3]
@test half_edges(g, 5) == [13,14,15,16]
@test σ(g, [1,2,3]) == [2,3,1]
@test σ(g, [13,14,15,16]) == [14,15,16,13]

faces = trace_faces(g)
sort!(faces, by=length)
@test map(length, faces) == [3,3,3,3,4]

outer_face_vs = sort(vertex(g, faces[end]))
inner_faces_vs = Set(sort(vertex(g, face)) for face in faces[1:end-1])
@test outer_face_vs == [1,2,3,4]
@test inner_faces_vs == Set([[1,2,5], [2,3,5], [3,4,5], [1,4,5]])

end
