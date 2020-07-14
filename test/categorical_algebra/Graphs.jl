module TestGraphs
using Test

import LightGraphs
using Catlab.CategoricalAlgebra.Graphs

# Graphs
########

g = Graph()
@test keys(g.indices) == (:src,:tgt)
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
@test collect(all_neighbors(g, 2)) == [1,3]

add_edge!(g, 1, 2)
@test ne(g) == 3
@test ne(g, 1, 2) == 2
@test collect(edges(g, 1, 2)) == [1,3]
@test outneighbors(g, 1) == [2,2]
@test inneighbors(g, 1) == []
@test LightGraphs.DiGraph(g) == LightGraphs.path_digraph(3)

g = Graph()
add_vertices!(g, 4)
add_edges!(g, [1,2,3], [2,3,4])
@test LightGraphs.DiGraph(g) == LightGraphs.path_digraph(4)

# Symmetric graphs
##################

g = SymmetricGraph()
@test keys(g.indices) == (:src,)

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
@test LightGraphs.Graph(g) == LightGraphs.path_graph(3)

g = SymmetricGraph()
add_vertices!(g, 4)
add_edges!(g, [1,2,3], [2,3,4])
lg = LightGraphs.DiGraph(4)
map((src, tgt) -> add_edge!(lg, src, tgt), [1,2,3,2,3,4], [2,3,4,1,2,3])
@test LightGraphs.DiGraph(g) == lg

# Property graphs
#################

g = PropertyGraph{String}()
add_vertex!(g, a="foo", b="bar")
@test nv(g) == 1
@test vprops(g, 1) == Dict(:a => "foo", :b => "bar")
@test get_vprop(g, 1, :b) == "bar"
set_vprop!(g, 1, :b, "baz")
@test get_vprop(g, 1, :b) == "baz"
add_vertices!(g, 2)
@test nv(g) == 3
@test vprops(g, 3) == Dict()

add_edge!(g, 1, 2, c="car")
@test ne(g) == 1
@test src(g, 1) == 1
@test tgt(g, 1) == 2
@test eprops(g, 1) == Dict(:c => "car")
@test get_eprop(g, 1, :c) == "car"
set_eprop!(g, 1, :c, "cat")
@test get_eprop(g, 1, :c) == "cat"
add_edges!(g, [2,2], [3,3])
set_eprop!(g, 2, :d, "dog")
set_eprop!(g, 3, :d, "dig")
@test src(g, [2,3]) == [2,2]
@test tgt(g, [2,3]) == [3,3]
@test (get_eprop(g, 2, :d), get_eprop(g, 3, :d)) == ("dog", "dig")

# Symmetric property graphs
###########################

g = SymmetricPropertyGraph{String}()
add_vertex!(g, a="aardvark")
@test vprops(g, 1) == Dict(:a => "aardvark")
add_vertex!(g)
@test vprops(g, 2) == Dict()

add_edge!(g, 1, 2, c="car")
@test ne(g) == 2
@test eprops(g, 1) == Dict(:c => "car")
@test eprops(g, 1) === eprops(g, 2)

end
