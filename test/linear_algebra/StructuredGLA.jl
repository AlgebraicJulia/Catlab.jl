module TestStructuredGraphicalLinearAlgebra
using Test

using Catlab, Catlab.Doctrines
using Catlab.LinearAlgebra.StructuredGraphicalLinearAlgebra

R = ℝ(FreeStructuredLinearFunctions.Ob)
A, B = Ob(FreeStructuredLinearFunctions, :A, :B)
f, g = Hom(:f, A, B), Hom(:g, A, B)
u, v = Hom(:u, R, A), Hom(:g, R, B)

# Domains and codomains
@test dom(plus(f,g)) == A
@test codom(plus(f,g)) == B

# Unicode syntax
@test f+g == plus(f,g)

# Banded Matrices
Dᵤ = diag(u)
@test dom(Dᵤ) == A
@test codom(Dᵤ) == A

Dᵥ = diag(v)
@test dom(Dᵥ) == B
@test codom(Dᵥ) == B

@test dom(Dᵥ⋅Dᵥ) == B
@test codom(Dᵥ⋅Dᵥ) == B

@test dom(Dᵥ⊕Dᵥ) == B⊕B
@test codom(Dᵥ⊕Dᵥ) == B⊕B
@test dom(Dᵤ⊕Dᵥ) == A⊕B
@test codom(Dᵤ⊕Dᵥ) == A⊕B

end