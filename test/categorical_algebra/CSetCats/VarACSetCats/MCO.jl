module TestVarACSetMCO 

using Catlab, Test
# Subobject graph
#-----------------
subG, subobjs = subobject_graph(path_graph(Graph, 3))


G′ = path_graph(WeightedGraph{Bool}, 3)
G′[:weight] = [false, AttrVar(add_part!(G′, :Weight))]
subG′, subobjs′ = subobject_graph(G′)
@test is_isomorphic(subG, subG′)
@test nparts(dom(hom(first(subobjs′))), :Weight) == 1
@test nparts(dom(hom(last(subobjs′))), :Weight) == 0

# Graph and ReflexiveGraph should have same subobject structure
subG2, _ = subobject_graph(path_graph(Graph, 2))
subRG2, sos = subobject_graph(path_graph(ReflexiveGraph, 2))
@test all(is_natural, hom.(sos))
@test is_isomorphic(subG2, subRG2)


end # module