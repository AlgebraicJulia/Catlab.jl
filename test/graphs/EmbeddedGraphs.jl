module TestEmbeddedGraphs
using Test

using Catlab.Graphs.BasicGraphs, Catlab.Graphs.EmbeddedGraphs

""" Wheel graph on `n` vertices with its unique planar embedding.
"""
function embedded_wheel_graph(T::Type, n::Int)
  @assert n >= 4
  n = n - 1 # Count using number of outer vertices.
  g = T()
  for i in 1:n # Outer corollas.
    add_corolla!(g, 3)
  end
  add_corolla!(g, n) # Inner corolla.
  pair_half_edges!(g, (3n+1):4n, reverse(2:3:3n)) # Inner <-> outer pairs.
  pair_half_edges!(g, 3:3:3n, circshift(1:3:3n, -1)) # Outer <-> outer pairs.
  return g
end

# Rotation graphs
#################

g = embedded_wheel_graph(RotationGraph, 5)
@test nv(g) == 5
@test length(half_edges(g)) == 16
@test half_edges(g, 1) == [1,2,3]
@test half_edges(g, 5) == [13,14,15,16]
@test σ(g, [1,2,3]) == [2,3,1]
@test σ(g, [13,14,15,16]) == [14,15,16,13]
@test α(g) == inv(g)

faces = trace_faces(g)
sort!(faces, by=length)
@test map(length, faces) == [3,3,3,3,4]

outer_face_vs = sort(vertex(g, faces[end]))
inner_faces_vs = Set(sort(vertex(g, face)) for face in faces[1:end-1])
@test outer_face_vs == [1,2,3,4]
@test inner_faces_vs == Set([[1,2,5], [2,3,5], [3,4,5], [1,4,5]])

# Rotation systems
##################

sys = embedded_wheel_graph(RotationSystem, 5)

vertices = trace_vertices(sys)
@test length(vertices) == 5
@test [1,2,3] in vertices
@test [13,14,15,16] in vertices

edges = trace_edges(sys)
@test length(edges) == 8
@test [3,4] in edges
@test [1,12] in edges

@test σ(sys) == σ(g)
@test α(sys) == inv(g)
@test trace_faces(sys) == trace_faces(g)

end
