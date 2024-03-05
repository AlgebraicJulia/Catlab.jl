module TestPropertyGraphs
using Test

using Catlab.Graphs.BasicGraphs, Catlab.Graphs.PropertyGraphs, Catlab.Graphs.BipartiteGraphs

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

# Bipartite property graphs
###########################

bg = BipartitePropertyGraph{String}()
add_vertex₁!(bg, a="alphonse", b="elric")
add_vertices₁!(bg, 1, a="ed", b="elric")
add_vertices₁!(bg, 2, f="rei", l="ayanami")
add_vertex₂!(bg, a="trisha", b="elric")
add_vertex₂!(bg, a="rurouni", b="kenshin")
add_vertices₂!(bg, 1, a="van", b="hohenheim")

@test_throws Exception add_edges₁₂!(bg, [1,1], [1,3,5], rel="childof")
add_edges₁₂!(bg, [1,1], [1,3], rel="childof")
@test_throws Exception add_edges₂₁!(bg, [1,3], [1,1,5], rel="parentof")
add_edges₂₁!(bg, [1,3], [1,1], rel="parentof")
add_edge₂₁!(bg, 3, 2, rel="parentof")

@test nv₁(bg) == 4
@test nv₂(bg) == 3
@test nv(bg) == (4,3)
@test vertices₁(bg) == 1:4
@test vertices₂(bg) == 1:3
@test vertices(bg) == (vertices₁(bg), vertices₂(bg))
@test ne(bg) == (2,3)
@test edges(bg) == (1:2, 1:3)

e = add_edge₁₂!(bg, 1, 2, a="mistake")
rem_edge₁₂!(bg, e)
@test e ∉ edges₁₂(bg)
e = add_edges₁₂!(bg, [1,1], [2,2], a="mistake")
rem_edges₁₂!(bg, e)
@test e ∉ edges₁₂(bg)

e = add_edge₂₁!(bg, 1, 2, a="mistake")
rem_edge₂₁!(bg, e)
@test e ∉ edges₂₁(bg)
e = add_edges₂₁!(bg, [1,1], [2,2], a="mistake")
rem_edges₂₁!(bg, e)
@test e ∉ edges₂₁(bg)
@test edges(bg) == (1:2, 1:3)

@test gprops(bg) isa Dict
@test v₁props(bg, 1) == Dict(:a=>"alphonse", :b=>"elric")
@test v₂props(bg, 1) == Dict(:a=>"trisha", :b=>"elric")
@test e₁₂props(bg, 1) == Dict(:rel=>"childof")
@test e₂₁props(bg, 1) == Dict(:rel=>"parentof")
@test get_v₁prop(bg, 1, :a) == "alphonse"
@test get_v₂prop(bg, 1, :a) == "trisha"
@test get_e₁₂prop(bg, 1, :rel) == "childof"
@test get_e₂₁prop(bg, 1, :rel) == "parentof"

set_v₁prop!(bg, 4, :f, "rei1")
@test get_v₁prop(bg, 4, :f) == "rei1"

set_v₂prop!(bg, 2, :a, "himura")
@test get_v₂prop(bg, 2, :a) == "himura"

set_e₁₂prop!(bg, 1, :rel, "childof1")
@test get_e₁₂prop(bg, 1, :rel) == "childof1"

set_e₂₁prop!(bg, 1, :rel, "parentof1")
@test get_e₂₁prop(bg, 1, :rel) == "parentof1"

set_v₁prop!(bg, 3:4, :f, "rei")
get_v₁prop(bg, 3:4, :f) == ["rei", "rei"]

set_v₂prop!(bg, 2, :a, "kenshin")
get_v₂prop(bg, 2, :a) == "kenshin"

set_e₁₂props!(bg, 1, rel="childof")
@test get_e₁₂prop(bg, 1:2, :rel) == ["childof", "childof"]

set_e₂₁props!(bg, 1, rel="parentof")
@test get_e₂₁prop(bg, 1:3, :rel) == ["parentof", "parentof", "parentof"]

end
