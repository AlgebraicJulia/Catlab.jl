module TestFinSets
using Test

using Catlab.Theories
using Catlab.CategoricalAlgebra.ShapeDiagrams, Catlab.CategoricalAlgebra.FinSets

f = FinOrdFunction([1,3,4], 5)
g = FinOrdFunction([1,1,2,2,3], 3)
h = FinOrdFunction([3,1,2], 3)

# Evaluation.
@test map(f, 1:3) == [1,3,4]
@test map(id(FinOrd(3)), 1:3) == [1,2,3]
@test map(FinOrdFunction(x -> (x % 3) + 1, 3, 3), 1:3) == [2,3,1]

# Category of finite ordinals.
@test dom(f) == FinOrd(3)
@test codom(f) == FinOrd(5)
@test compose(f,g) == FinOrdFunction([1,2,2], 3)
@test compose(g,h) == FinOrdFunction([3,3,1,1,2], 3)
@test compose(compose(f,g),h) == compose(f,compose(g,h))
@test compose(id(dom(f)),f) == f
@test compose(f,id(codom(f))) == f

# Pushout from the empty set: the degenerate case of the coproduct.
f, g = FinOrdFunction([], 2), FinOrdFunction([], 3)
cospan = pushout(Span(f,g))
@test base(cospan) == FinOrd(5)
@test force(left(cospan)) == FinOrdFunction([1,2], 5)
@test force(right(cospan)) == FinOrdFunction([3,4,5], 5)

# Pushout from a singleton set.
f, g = FinOrdFunction([1], 2), FinOrdFunction([2], 3)
cospan = pushout(Span(f,g))
@test base(cospan) == FinOrd(4)
h, k = force(left(cospan)), force(right(cospan))
@test compose(f,h) == compose(g,k)
@test h == FinOrdFunction([1,2], 4)
@test k == FinOrdFunction([3,1,4], 4)

# Pushout from a two-element set, with non-injective legs.
f, g = FinOrdFunction([1,1], 2), FinOrdFunction([1,2], 2)
cospan = pushout(Span(f,g))
@test base(cospan) == FinOrd(2)
h, k = force(left(cospan)), force(right(cospan))
@test compose(f,h) == compose(g,k)
@test h == FinOrdFunction([1,2], 2)
@test k == FinOrdFunction([1,1], 2)

end
