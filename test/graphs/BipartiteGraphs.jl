module TestBipartiteGraphs
using Test

using Catlab.Graphs.BasicGraphs, Catlab.Graphs.BipartiteGraphs

# Undirected bipartite graphs
#############################

g = UndirectedBipartiteGraph()
add_vertices₁!(g, 2)
add_vertices₂!(g, 3)
@test (nv₁(g), nv₂(g)) == (2,3)
@test (vertices₁(g), vertices₂(g)) == (1:2, 1:3)
@test nv(g) == (2,3)
@test vertices(g) == (1:2, 1:3)
@test g == UndirectedBipartiteGraph(2, 3)

add_edge!(g, 1, 1)
add_edges!(g, [2,2], [2,3])
@test ne(g) == 3
@test edges(g) == 1:3
@test (src(g), tgt(g)) == ([1,2,2], [1,2,3])

rem_edge!(g, 1, 1)
@test ne(g) == 2
rem_vertex₁!(g, 1)
rem_vertex₂!(g, 1)
@test nv(g) == (1,2)
@test ne(g) == 2

# Bipartite graphs
##################

g = BipartiteGraph(2, 3)
@test nv(g) == (2, 3)

add_edge₁₂!(g, 1, 2)
add_edge₂₁!(g, 1, 1)
add_edges₁₂!(g, [2,2], [3,3])
add_edges₂₁!(g, [2,3], [1,1])
@test (ne₁₂(g), ne₂₁(g)) == (3,3)
@test (edges₁₂(g), edges₂₁(g)) == (1:3, 1:3)
@test ne(g) == (3,3)
@test edges(g) == (1:3, 1:3)
@test (src₁(g), tgt₂(g)) == ([1,2,2], [2,3,3])
@test (src₂(g), tgt₁(g)) == ([1,2,3], [1,1,1])

rem_edge₁₂!(g, 1, 2)
@test (src₁(g), tgt₂(g)) == ([2,2], [3,3])
rem_edge₂₁!(g, 1, 1)
@test (src₂(g), tgt₁(g)) == ([3,2], [1,1])
rem_vertex₁!(g, 1)
@test nv(g) == (1,3)
@test ne(g) == (2,0)
rem_vertex₂!(g, 3)
@test nv(g) == (1,2)
@test ne(g) == (0,0)

end
