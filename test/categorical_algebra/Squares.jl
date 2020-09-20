module TestSquares
using Test
using Catlab.Theories, Catlab.CategoricalAlgebra
using Catlab.CategoricalAlgebra.FinSets
using Catlab.CategoricalAlgebra.Squares

t  = FinFunction([1,2,4], 5)
l  = FinFunction([1,2,3], 3)
b = FinFunction([2,3,1], 3)
f  = FinFunction([2,3,2,1,3], 3)

α = SquareDiagram(t, b, l, f)

t₁ = FinFunction([1,1,1,1,1], 1)
r  = FinFunction([1], 1)
b₁ = FinFunction([1,1,1], 1)

β = SquareDiagram(t₁, b₁, f, r)
γ = composeH(α, β)
@test top(γ) == t⋅t₁
@test bottom(γ) == b⋅b₁
@test left(γ) == left(α)
@test right(γ) == right(β)
end #module
