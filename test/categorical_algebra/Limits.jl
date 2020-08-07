module TestLimits
using Test

using Catlab.Theories, Catlab.CategoricalAlgebra.Limits

A, B, C = Ob(FreeCategory, :A, :B, :C)

# Cones.
f, g = Hom(:f, C, A), Hom(:g, C, B)
cone = Cone(C,[f,g])
@test apex(cone) == C
@test leg(cone,1) == f
@test leg(cone,2) == g
f = Hom(:f, A, B)
@test_throws Exception Cone(C,[f,g])

# Cocones.
f, g = Hom(:f, A, C), Hom(:g, B, C)
cocone = Cocone(C,[f,g])
@test base(cocone) == C
@test leg(cocone,1) == f
@test leg(cocone,2) == g
f = Hom(:f, A, B)
@test_throws Exception Cocone(C,[f,g])

end
