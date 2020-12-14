module TestCommutativeDiagrams
using Test

using Catlab.Theories, Catlab.CategoricalAlgebra.FinSets
using Catlab.CategoricalAlgebra.CommutativeDiagrams

A, B, C, D = Ob(FreeCategory, :A, :B, :C, :D)

# Commutative squares
#####################

l, t, b, r = Hom(:lef, A,B), Hom(:top, A, C), Hom(:bot, B, D), Hom(:rht, C,D)
sq1 = SquareDiagram(t, b, l, r)

@test_throws AssertionError composeH(sq1, sq1)

l, t, b, r = Hom(:lef, A,B), Hom(:top, A, A), Hom(:bot, B, B), Hom(:rht, A,B)
rr = Hom(:rr, A,B)
sq2 = SquareDiagram(t, b, l, r)
sq3 = composeH(sq2, SquareDiagram(t, b, r, rr))
@test left(sq3)   == l
@test top(sq3)    == compose(t,t)
@test bottom(sq3) == compose(b,b)
@test right(sq3)  == rr

@test_throws AssertionError composeV(sq2, sq2)

ll = Hom(:ll, B, A)
rr = Hom(:rr, B, A)
sq4 = composeV(sq2, SquareDiagram(b, t, ll, rr))
@test left(sq4)    == compose(l, ll)
@test right(sq4)  == compose(r, rr)
@test top(sq4)   == t
@test bottom(sq4) == t

@test hom(sq4) == [top(sq4), bottom(sq4), left(sq4), right(sq4)]

# Double category of squares
#---------------------------

t  = FinFunction([1,2,4], 5)
l  = FinFunction([1,2,3], 3)
b  = FinFunction([2,3,1], 3)
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

t = FinFunction([1,2,4], 5)
b = FinFunction([2,1,3], 3)
l = FinFunction([2,1,3], 3)
r = FinFunction([1,2,2,3,3], 3)
α = SquareDiagram(t,b,l,r)
β = SquareDiagram(FinFunction([1,2,1,2,1], 2),
                  FinFunction([1,1,1],1),
                  FinFunction([1,2,2,3,3], 3),
                  FinFunction([1,1],1)
)
γ = composeH(α, β)
@test collect(top(γ)) == [1,2,2]
@test collect(bottom(γ)) == [1,1,1]

α = SquareDiagram(l,r, t,b)
β = SquareDiagram(FinFunction([1,2,2,3,3], 3),
                  FinFunction([1,1],1),
                  FinFunction([1,2,1,2,1], 2),
                  FinFunction([1,1,1],1)
)
γ = composeV(α, β)
@test_throws AssertionError composeH(α, β)
@test collect(left(γ)) == [1,2,2]
@test collect(right(γ)) == [1,1,1]

@test collect(idH(FinSet(3))) == collect(1:3)
@test collect(idV(FinSet(5))) == collect(1:5)
@test collect(idH(FinSet(0))) == []

@test collect(composeH(FinFunction([2,1], 3), FinFunction([2, 1, 3]))) == [1,2]
@test collect(composeV(FinFunction([2,1], 3), FinFunction([2, 1, 3]))) == [1,2]

end
