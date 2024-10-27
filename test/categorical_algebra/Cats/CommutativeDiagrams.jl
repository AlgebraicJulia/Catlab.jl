module TestCommutativeDiagrams
using Test

using Catlab.Theories
using Catlab.CategoricalAlgebra.CommutativeDiagrams

# Commutative squares
#####################

A, B, C, D, X, Y = Ob(FreeCategory, :A, :B, :C, :D, :X, :Y)
f, g, m, n = Hom(:f, A, C), Hom(:g, B, D), Hom(:m, A, B), Hom(:n, C, D)

α = SquareDiagram(m, n, f, g)
@test top(α) == m
@test bottom(α) == n
@test left(α) == f
@test right(α) == g
@test ob(α) == [A, B, C, D]
@test hom(α) == [m, n, f, g]

# Double category of squares
#---------------------------

@test hom(dom(α)) == m
@test hom(codom(α)) == n
@test hom(src(α)) == f
@test hom(tgt(α)) == g

@test ob(src(dom(α))) == A
@test ob(tgt(dom(α))) == B
@test ob(codom(src(α))) == C
@test ob(codom(tgt(α))) == D

@test_throws ErrorException compose(α, α)
@test compose(id(dom(α)), α) == α
@test compose(α, id(codom(α))) == α

h, k, p = Hom(:h, C, X),Hom(:g, D, Y), Hom(:p, X, Y)
β = SquareDiagram(n, p, h, k)
@test compose(α, β) == SquareDiagram(m, p, f⋅h, g⋅k)

@test_throws ErrorException pcompose(α, α)
@test pcompose(pid(src(α)), α) == α
@test pcompose(α, pid(tgt(α))) == α

h, p, q = Hom(:h, X, Y), Hom(:p, B, X), Hom(:q, D, Y)
β = SquareDiagram(p, q, g, h)
@test pcompose(α, β) == SquareDiagram(m⋅p, n⋅q, f, h)

end
