module TestFinSets
using Test

using Catlab.Theories
using Catlab.CategoricalAlgebra.ShapeDiagrams, Catlab.CategoricalAlgebra.FinSets

# Category of finite ordinals
#############################

f = FinOrdFunction([1,3,4], 5)
g = FinOrdFunction([1,1,2,2,3], 3)
h = FinOrdFunction([3,1,2], 3)

# Evaluation.
@test map(f, 1:3) == [1,3,4]
@test map(id(FinOrd(3)), 1:3) == [1,2,3]
@test map(FinOrdFunction(x -> (x % 3) + 1, 3, 3), 1:3) == [2,3,1]

# Composition and identities.
@test dom(f) == FinOrd(3)
@test codom(f) == FinOrd(5)
@test compose(f,g) == FinOrdFunction([1,2,2], 3)
@test compose(g,h) == FinOrdFunction([3,3,1,1,2], 3)
@test compose(compose(f,g),h) == compose(f,compose(g,h))
@test force(compose(id(dom(f)),f)) == f
@test force(compose(f,id(codom(f)))) == f

# Limits
########

# Terminal object.
@test terminal(FinOrd) == FinOrd(1)

# Product.
span = product(FinOrd(2), FinOrd(3))
@test apex(span) == FinOrd(6)
@test force(left(span)) == FinOrdFunction([1,2,1,2,1,2])
@test force(right(span)) == FinOrdFunction([1,1,2,2,3,3])

# Equalizer.
f, g = FinOrdFunction([1,2,3]), FinOrdFunction([3,2,1])
@test equalizer(f,g) == FinOrdFunction([2], 3)

# Equalizer in case of identical functions.
f = FinOrdFunction([4,2,3,1], 5)
@test equalizer(f,f) == force(id(FinOrd(4)))

# Equalizer matching nothing.
f, g = id(FinOrd(5)), FinOrdFunction([2,3,4,5,1], 5)
@test equalizer(f,g) == FinOrdFunction(Int[], 5)

# Pullback.
span = pullback(Cospan(FinOrdFunction([1,1,3,2],4), FinOrdFunction([1,1,4,2],4)))
@test apex(span) == FinOrd(5)
@test force(left(span)) == FinOrdFunction([1,2,1,2,4], 4)
@test force(right(span)) == FinOrdFunction([1,1,2,2,4], 4)

# Pullback from a singleton set: the degenerate case of a product.
span = pullback(Cospan(FinOrdFunction([1,1]), FinOrdFunction([1,1,1])))
@test apex(span) == FinOrd(6)
@test force(left(span)) == FinOrdFunction([1,2,1,2,1,2])
@test force(right(span)) == FinOrdFunction([1,1,2,2,3,3])

# Colimits
##########

# Initial object.
@test initial(FinOrd) == FinOrd(0)

# Coproduct.
cospan = coproduct(FinOrd(2), FinOrd(3))
@test base(cospan) == FinOrd(5)
@test left(cospan) == FinOrdFunction([1,2], 5)
@test right(cospan) == FinOrdFunction([3,4,5], 5)

# Coequalizer from a singleton set.
f, g = FinOrdFunction([1], 3), FinOrdFunction([3], 3)
@test coequalizer(f,g) == FinOrdFunction([1,2,1], 2)

# Coequalizer in case of identical functions.
f = FinOrdFunction([4,2,3,1], 5)
@test coequalizer(f,f) == force(id(FinOrd(5)))

# Coequalizer identifying everything.
f, g = id(FinOrd(5)), FinOrdFunction([2,3,4,5,1], 5)
@test coequalizer(f,g) == FinOrdFunction(repeat([1],5))

# Pushout from the empty set: the degenerate case of the coproduct.
f, g = FinOrdFunction(Int[], 2), FinOrdFunction(Int[], 3)
cospan = pushout(Span(f,g))
@test base(cospan) == FinOrd(5)
@test left(cospan) == FinOrdFunction([1,2], 5)
@test right(cospan) == FinOrdFunction([3,4,5], 5)

# Pushout from a singleton set.
f, g = FinOrdFunction([1], 2), FinOrdFunction([2], 3)
cospan = pushout(Span(f,g))
@test base(cospan) == FinOrd(4)
h, k = left(cospan), right(cospan)
@test compose(f,h) == compose(g,k)
@test h == FinOrdFunction([1,2], 4)
@test k == FinOrdFunction([3,1,4], 4)

# Pushout from a two-element set, with non-injective legs.
f, g = FinOrdFunction([1,1], 2), FinOrdFunction([1,2], 2)
cospan = pushout(Span(f,g))
@test base(cospan) == FinOrd(2)
h, k = left(cospan), right(cospan)
@test compose(f,h) == compose(g,k)
@test h == FinOrdFunction([1,2], 2)
@test k == FinOrdFunction([1,1], 2)

end
