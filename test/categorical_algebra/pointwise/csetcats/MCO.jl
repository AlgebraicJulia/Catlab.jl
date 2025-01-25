module TestCSetMCO 

using Test, Catlab 

# Enumeration of subobjects 
###########################

G = path_graph(Graph, 3)
subG, subobjs = subobject_graph(G)
@test length(subobjs) == 13 # ⊤,2x •→• •,2x •→•, •••,3x ••, 3x •, ⊥
@test length(incident(subG, 13, :src)) == 13 # ⊥ is initial
@test length(incident(subG, 1, :src)) == 1 # ⊤ is terminal

# With attributes
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

# Partial overlaps 
G, H = path_graph.(Graph, 2:3)
os = collect(partial_overlaps(G, G))
@test length(os) == 7 # ⊤, ••, 4× •, ⊥

po = partial_overlaps([G, H])
@test length(collect(po))==12  # 2×⊤, 3×••, 6× •, ⊥
@test all(m -> apex(m) == G, Iterators.take(po, 2)) # first two are •→•
@test all(m -> apex(m) == Graph(2), 
          Iterators.take(Iterators.drop(po, 2), 3)) # next three are • •

end # module
