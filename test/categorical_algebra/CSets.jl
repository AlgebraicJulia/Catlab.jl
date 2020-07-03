module TestCSets
using Test

using LightGraphs
using Catlab.CategoricalAlgebra.CSets

# Graphs
########

g = CSets.Graph()
add_vertex!(g)
add_vertices!(g, 2)
@test nv(g) == 3
@test ne(g) == 0

add_edge!(g, 1, 2)
add_edge!(g, 2, 3)
@test ne(g) == 2
@test ne(g, 1, 2) == 1
@test has_edge(g, 1, 2)
@test !has_edge(g, 1, 3)
@test outneighbors(g, 2) == [3]
@test inneighbors(g, 2) == [1]
@test all_neighbors(g, 2) == [1,3]

add_edge!(g, 1, 2)
@test ne(g) == 3
@test ne(g, 1, 2) == 2
@test outneighbors(g, 1) == [2,2]
@test inneighbors(g, 1) == []

end
