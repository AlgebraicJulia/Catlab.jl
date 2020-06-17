module TestFinSets
using Test

using Catlab.Theories
using Catlab.CategoricalAlgebra.ShapeDiagrams, Catlab.CategoricalAlgebra.FinSets

f = FinOrdFunction([1,3,4], 5)
g = FinOrdFunction([1,1,2,2,3], 3)
h = FinOrdFunction([3,1,2], 3)
@test [f(1),f(2),f(3)] == [1,3,4]

# Category of finite ordinals
@test dom(f) == FinOrd(3)
@test codom(f) == FinOrd(5)
@test compose(f,g) == FinOrdFunction([1,2,2], 3)
@test compose(g,h) == FinOrdFunction([3,3,1,1,2], 3)
@test compose(compose(f,g),h) == compose(f,compose(g,h))
@test compose(id(dom(f)),f) == f
@test compose(f,id(codom(f))) == f

# Pushout.
f, g = FinOrdFunction([1], 2), FinOrdFunction([2], 3)
cospan = pushout(Span(f,g))
@test base(cospan) == FinOrd(4)
h, k = left(cospan), right(cospan)
@test compose(f,h) == compose(g,k)
@test h == FinOrdFunction([1,2], 4)
@test k == FinOrdFunction([3,1,4], 4)

end
