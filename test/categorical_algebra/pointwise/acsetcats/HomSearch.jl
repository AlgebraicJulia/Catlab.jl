module TestACSetHomSearch 

using Catlab, Test

# Labeled graphs
#---------------

g = cycle_graph(LabeledGraph{Symbol}, 4, V=(label=[:a,:b,:c,:d],))
h = cycle_graph(LabeledGraph{Symbol}, 4, V=(label=[:c,:d,:a,:b],))
α = ACSetTransformation((V=[3,4,1,2], E=[3,4,1,2]), g, h)
@test homomorphism(g, h) == α
# @test homomorphism(g, h, alg=HomomorphismQuery()) == α # TODO
h = cycle_graph(LabeledGraph{Symbol}, 4, V=(label=[:a,:b,:d,:c],))
@test !is_homomorphic(g, h)
# @test !is_homomorphic(g, h, alg=HomomorphismQuery()) # TODO

# THIS WOULD BE EASIER IF THE ACSETCat INTERFACE
# had coerce_ob_component and coerce_attr_component
# instead of just a 'coerce' method

# As a macro
#-----------

g = cycle_graph(LabeledGraph{String}, 4, V=(label=["a","b","c","d"],))
h = cycle_graph(LabeledGraph{String}, 4, V=(label=["b","c","d","a"],))
α = @acset_transformation g h
β = @acset_transformation g h begin
  V = [4,1,2,3]
  E = [4,1,2,3]
end monic=true
γ = @acset_transformation g h begin end monic=[:V]
@test α[:V](1) == 4
@test α[:E](1) == 4
@test α == β == γ

x = @acset Graph begin
  V = 2
  E = 2
  src = [1,1]
  tgt = [2,2]
end
@test length(@acset_transformations x x) == length(@acset_transformations x x monic=[:V]) == 4
@test length(@acset_transformations x x monic = true) == 2
@test length(@acset_transformations x x begin V=[1,2] end monic = [:E]) == 2
# @test length(@acset_transformations x x begin V = Dict(1=>1) end monic = [:E]) == 2 # TODO Unclear what to do with Dicts
@test_throws ErrorException @acset_transformation g h begin V = [4,3,2,1]; E = [1,2,3,4] end

end # module
