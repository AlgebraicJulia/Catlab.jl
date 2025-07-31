module TestDynamicCSets

using Catlab, Test

X,Y = [DynamicACSet("WG", SchWeightedGraph; type_assignment=Dict(:Weight=>Float64)) 
      for _ in 1:2]
add_parts!(X, :V, 2)
add_parts!(X, :E, 3; src=[1,1,2],tgt=[2,1,1,],weight=[4.,3.,4.])
add_parts!(Y, :V, 2)
add_part!(Y, :E; src=1, tgt=2, weight=4.)

const 𝒞 = ACSetCategory(X)

f = ACSetTransformation(X,X; V=[1,2], E=[1,2,3], cat=𝒞)
@test is_natural(f)
@test !is_natural(ACSetTransformation(X,X; V=[2,1], E=[1,2,3], cat=𝒞)) # bad homs
@test !is_natural(ACSetTransformation(X,X; V=[1,1], E=[2,1,3], cat=𝒞)) # bad attrs
@test components(f) == (V=FinFunction([1,2]), E=FinFunction([1,2,3]), 
                        Weight=nothing)

@test_throws MethodError ACSetTransformation(Y,X; V=[1,2], E=1, cat=𝒞)
g = ACSetTransformation(Y,X; V=[1,2], E=[1], cat=𝒞)
@test is_natural(g)
@test compose[𝒞](g,f) ≃ g


G, H = [DynamicACSet("Grph",SchGraph) for _ in 1:2];
const Grph = ACSetCategory(G)

add_parts!(G, :V, 2); 
add_parts!(H,:V,2);
add_part!(G, :E; src=1, tgt=2)
add_parts!(H, :E,2; src=[1,2], tgt=[1,2])
hs = homomorphisms(G,H)
@test length(hs) == 2
@test all(is_natural, hs)

@test is_natural(id[Grph](G); cat=𝒞)

end # module
