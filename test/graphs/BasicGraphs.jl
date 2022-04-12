module TestBasicGraphs
using Test

import Graphs as SimpleGraphs
import MetaGraphs

using Catlab.Graphs.BasicGraphs

# Graphs
########

g = Graph()
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
@test degree(g, 2) == 2
@test collect(all_neighbors(g, 2)) == [1,3]

add_edge!(g, 1, 2)
@test ne(g) == 3
@test ne(g, 1, 2) == 2
@test collect(edges(g, 1, 2)) == [1,3]
@test outneighbors(g, 1) == [2,2]
@test inneighbors(g, 1) == []
@test degree(g, 1) == 2
@test SimpleGraphs.DiGraph(g) == SimpleGraphs.path_digraph(3)

g = Graph(4)
add_edges!(g, [1,2,3], [2,3,4])
@test SimpleGraphs.DiGraph(g) == SimpleGraphs.path_digraph(4)
@test Graph(SimpleGraphs.path_digraph(4)) == g

rem_edge!(g, 3, 4)
@test ne(g) == 2
@test src(g) == [1,2]
@test tgt(g) == [2,3]
rem_vertex!(g, 2)
@test nv(g) == 3
@test ne(g) == 0

# Error handling.
g = Graph(2)
add_edge!(g, 1, 2)
@test_throws Exception add_edge!(g, 2, 3) # nonexistent target vertex
@test ne(g) == 1
@test isempty(outneighbors(g, 2))

# Induced subgraphs.
g = Graph(3)
add_edges!(g, [1,1,2], [3,3,3])
sub = induced_subgraph(g, [1,3])
@test nv(sub) == 2
@test src(sub) == [1,1]
@test tgt(sub) == [2,2]

# Symmetric graphs
##################

g = SymmetricGraph()

add_vertices!(g, 3)
@test nv(g) == 3
@test ne(g) == 0

add_edge!(g, 1, 2)
add_edge!(g, 2, 3)
@test ne(g) == 4
@test collect(edges(g, 1, 2)) == [1]
@test neighbors(g, 1) == [2]
@test neighbors(g, 2) == [1,3]
@test neighbors(g, 3) == [2]
@test SimpleGraphs.Graph(g) == SimpleGraphs.path_graph(3)
@test SymmetricGraph(SimpleGraphs.path_graph(3)) == g

g = SymmetricGraph(4)
add_edges!(g, [1,2,3], [2,3,4])
lg = SimpleGraphs.DiGraph(map(SimpleGraphs.Edge, [1,2,3,2,3,4], [2,3,4,1,2,3]))
@test SimpleGraphs.DiGraph(g) == lg

rem_edge!(g, 3, 4)
@test ne(g) == 4
@test neighbors(g, 3) == [2]
@test neighbors(g, 4) == []
rem_vertex!(g, 2)
@test nv(g) == 3
@test ne(g) == 0

# Reflexive graphs
##################

g = ReflexiveGraph()
add_vertex!(g)
add_vertices!(g, 2)
@test nv(g) == 3
@test ne(g) == 3
@test refl(g,1) == 1
@test refl(g) == [1,2,3]
@test src(g) == [1,2,3]
@test tgt(g) == [1,2,3]

add_edges!(g, [1,2], [2,3])
add_edge!(g, 1, 3)
@test ne(g) == 6
@test src(g, 4:6) == [1,2,1]
@test tgt(g, 4:6) == [2,3,3]

g = ReflexiveGraph(4)
add_edges!(g, [1,2,3], [2,3,4])
rem_edge!(g, 3, 4)
@test ne(g) == 6
@test src(g, 5:6) == [1,2]
@test tgt(g, 5:6) == [2,3]
rem_vertex!(g, 2)
@test nv(g) == 3
@test ne(g) == 3
@test refl(g) == [1,2,3]
@test src(g) == [1,2,3]
@test tgt(g) == [1,2,3]

# Symmetric reflexive graphs
############################

g = SymmetricReflexiveGraph()
add_vertex!(g)
add_vertices!(g, 2)
@test nv(g) == 3
@test refl(g) == [1,2,3]
@test inv(g) == [1,2,3]
@test src(g) == [1,2,3]
@test tgt(g) == [1,2,3]

add_edge!(g, 1, 3)
@test ne(g) == 5
@test src(g, 4:5) == [1,3]
@test tgt(g, 4:5) == [3,1]
@test inv(g, 4:5) == [5,4]

g = SymmetricReflexiveGraph(4)
add_edges!(g, [1,2,3], [2,3,4])
rem_edge!(g, 3, 4)
@test ne(g) == 8
rem_vertex!(g, 2)
@test nv(g) == 3
@test ne(g) == 3

# Half-edge graphs
##################

g = HalfEdgeGraph()

add_vertices!(g, 2)
@test nv(g) == 2
@test isempty(half_edges(g))

add_edge!(g, 1, 2)
add_edge!(g, 2, 1)
@test collect(half_edges(g)) == [1,2,3,4]
@test vertex(g) == [1,2,2,1]
@test inv(g) == [2,1,4,3]
@test half_edges(g, 1) == [1,4]
@test half_edges(g, 2) == [2,3]

add_dangling_edge!(g, 1)
add_dangling_edges!(g, [2,2])
@test length(half_edges(g)) == 7
@test vertex(g, 5:7) == [1,2,2]
@test inv(g, 5:7) == [5,6,7]

g = HalfEdgeGraph(4)
add_edges!(g, [1,2,3], [2,3,4])
lg = SimpleGraphs.Graph(map(SimpleGraphs.Edge, [1,2,3], [2,3,4]))
@test SimpleGraphs.Graph(g) == lg

rem_edge!(g, 3, 4)
@test Set(zip(vertex(g), vertex(g,inv(g)))) == Set([(1,2),(2,1),(2,3),(3,2)])
add_edge!(g, 3, 4)
rem_edge!(g, last(half_edges(g)))
@test Set(zip(vertex(g), vertex(g,inv(g)))) == Set([(1,2),(2,1),(2,3),(3,2)])
rem_vertex!(g, 2)
@test nv(g) == 3
@test isempty(half_edges(g))

# Weighted graphs
#################

g = WeightedGraph{Float64}(4)
add_edges!(g, 1:3, 2:4, weight=[0.25, 0.5, 0.75])
@test weight(g, 1) == 0.25
@test weight(g) == [0.25, 0.5, 0.75]

mg = MetaGraphs.MetaDiGraph{Int,Float64}(4)
MetaGraphs.add_edge!(mg, 1, 2, :weight, 0.25)
MetaGraphs.add_edge!(mg, 2, 3, :weight, 0.5)
MetaGraphs.add_edge!(mg, 3, 4, :weight, 0.75)
@test MetaGraphs.MetaDiGraph(g) == mg

end
