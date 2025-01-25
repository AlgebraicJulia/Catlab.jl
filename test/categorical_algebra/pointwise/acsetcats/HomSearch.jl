module TestACSetHomSearch 

using Test, Catlab

g = cycle_graph(LabeledGraph{Symbol}, 4, V=(label=[:a,:b,:c,:d],))
h = cycle_graph(LabeledGraph{Symbol}, 4, V=(label=[:c,:d,:a,:b],))
α = ACSetTransformation((V=[3,4,1,2], E=[3,4,1,2]), g, h)
@test homomorphism(g, h) == α
@test homomorphism(g, h, alg=HomomorphismQuery()) == α
h = cycle_graph(LabeledGraph{Symbol}, 4, V=(label=[:a,:b,:d,:c],))
@test !is_homomorphic(g, h)
@test !is_homomorphic(g, h, alg=HomomorphismQuery())

end # module
