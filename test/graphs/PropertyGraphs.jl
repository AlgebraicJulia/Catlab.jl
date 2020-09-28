module TestPropertyGraphs
using Test

using Catlab.Graphs.BasicGraphs, Catlab.Graphs.PropertyGraphs

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
set_vprop!(g, 1:3, :b, ["bar", "baz", "biz"])
@test get_vprop(g, 1:3, :b) == ["bar", "baz", "biz"]

add_edge!(g, 1, 2, c="car")
@test ne(g) == 1
@test src(g, 1) == 1
@test tgt(g, 1) == 2
@test eprops(g, 1) == Dict(:c => "car")
@test get_eprop(g, 1, :c) == "car"
set_eprop!(g, 1, :c, "cat")
@test get_eprop(g, 1, :c) == "cat"
add_edges!(g, [2,2], [3,3])
set_eprop!(g, 2:3, :d, ["dog", "dig"])
@test src(g, [2,3]) == [2,2]
@test tgt(g, [2,3]) == [3,3]
@test get_eprop(g, 2:3, :d) == ["dog", "dig"]

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
