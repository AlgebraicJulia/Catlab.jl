module TestACSetFunctors 

using Catlab, Test

g = path_graph(WeightedGraph{Float64}, 3, E=(weight=[0.5,1.5],))

C = infer_acset_cat(g)
CC = CollageCat(C)

impl_type(Category(CC), :Hom)


G = FinDomFunctor(g)

@test is_functorial(G)

V,E,src,tgt,Weight,weight = generators(SchWeightedGraph)

@test ob_map(G, V) == FinSetInt(3)

@test ob_map(G, Weight) == TaggedElem(nothing, :Weight)

@test hom_map(G, weight) == TaggedElem(FinDomFunction([0.5, 1.5], SetOb(Float64)), :Weight)

end # module
