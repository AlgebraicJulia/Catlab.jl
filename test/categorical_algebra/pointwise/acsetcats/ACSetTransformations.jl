module TestACSetTransformations 

using Catlab, Test

𝒞 = ACSetCategory(WeightedGraph{Float64}()) # infer we want ACSets

# Constructors and accessors. Test type conversion as well Int -> Float64
g = path_graph(WeightedGraph{Float64}, 2, E=(weight=2,))
h = path_graph(WeightedGraph{Float64}, 4, E=(weight=[1,2,3],))
@test_throws MethodError ACSetTransformation((V=[2,3], E=2), g, h)
α = ACSetTransformation((V=[2,3], E=[2]), g, h; cat=𝒞)
@test length(components(α)) == 3

@test is_monic(α; cat=𝒞)

# Naturality.
@test is_natural(α)
β = ACSetTransformation((V=[2,1], E=[2]), g, h)
@test !is_natural(β) # Preserves weight but not graph homomorphism
β = ACSetTransformation((V=[1,2], E=[1]), g, h)
@test !is_natural(β) # Graph homomorphism but does not preserve weight
β = ACSetTransformation((V=[1,3], E=[1]), g, h)
uns = naturality_failures(β)
@test collect(uns[:src]) == [] 
@test collect(uns[:tgt]) == [(1,2,3)] 
@test collect(uns[:weight]) == [(1, 1.,2.)]

# Monic / epic
@test is_epic(id[𝒞](g))

end # module
