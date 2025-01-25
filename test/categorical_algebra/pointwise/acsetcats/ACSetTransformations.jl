module TestACSetTransformations 

using Catlab, Test

# Constructors and accessors. Test type conversion as well Int -> Float64
g = path_graph(WeightedGraph{Float64}, 2, E=(weight=2,))
h = path_graph(WeightedGraph{Float64}, 4, E=(weight=[1,2,3],))
@test_throws ErrorException ACSetTransformation((V=[2,3], E=2), g, h)
α = ACSetTransformation((V=[2,3], E=[2]), g, h)
@test length(components(α)) == 3

# Naturality.
@test is_natural(α)
β = ACSetTransformation((V=[2,1], E=[2]), g, h)
@test !is_natural(β) # Preserves weight but not graph homomorphism
β = ACSetTransformation((V=[1,2], E=[1]), g, h)
@test !is_natural(β) # Graph homomorphism but does not preserve weight
β = ACSetTransformation((V=[1,3], E=[1]), g, h)
uns = naturality_failures(β)
@test collect(uns[:src]) == [] && collect(uns[:tgt]) == [(1,2,3)] &&
  collect(uns[:weight]) == [(1,1.0,2.0)]


# Dynamic ACSets
#################


X,Y = [DynamicACSet("WG", SchWeightedGraph; type_assignment=Dict(:Weight=>Float64)) 
for _ in 1:2]
add_parts!(X, :V, 2)
add_parts!(X, :E, 3; src=[1,1,2],tgt=[2,1,1,],weight=[4.,3.,4.])
add_parts!(Y, :V, 2)
add_part!(Y, :E; src=1, tgt=2, weight=4.)

f = ACSetTransformation(X,X; V=[1,2], E=[1,2,3])
@test is_natural(f)
@test !is_natural(ACSetTransformation(X,X; V=[2,1], E=[1,2,3])) # bad homs
@test !is_natural(ACSetTransformation(X,X; V=[1,1], E=[2,1,3])) # bad attrs
@test components(f) == (V=FinFunction([1,2]), E=FinFunction([1,2,3]), 
                  Weight=VarFunction{Float64}([], FinSet(0)))

@test_throws ErrorException ACSetTransformation(Y,X; V=[1,2], E=1)
g = ACSetTransformation(Y,X; V=[1,2], E=[1])
@test is_natural(g)
@test compose(g,f) |> force == g

end # module
