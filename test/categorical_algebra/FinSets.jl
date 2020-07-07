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

# Binary Product.
span = product(FinOrd(2), FinOrd(3))
@test apex(span) == FinOrd(6)
@test force(left(span)) == FinOrdFunction([1,2,1,2,1,2])
@test force(right(span)) == FinOrdFunction([1,1,2,2,3,3])

# N-ary Product.
cone = product([FinOrd(2), FinOrd(3)])
@test apex(cone) == FinOrd(6)
@test force(leg(cone,1)) == FinOrdFunction([1,2,1,2,1,2])
@test force(leg(cone,2)) == FinOrdFunction([1,1,2,2,3,3])
@test apex(product(FinOrd[])) == FinOrd(1)

# Equalizer.
f, g = FinOrdFunction([1,2,3]), FinOrdFunction([3,2,1])
@test equalizer(f,g) == FinOrdFunction([2], 3)
@test equalizer([f,g]) == FinOrdFunction([2], 3)

# Equalizer in case of identical functions.
f = FinOrdFunction([4,2,3,1], 5)
@test equalizer(f,f) == force(id(FinOrd(4)))
@test equalizer([f,f]) == force(id(FinOrd(4)))

# Equalizer matching nothing.
f, g = id(FinOrd(5)), FinOrdFunction([2,3,4,5,1], 5)
@test equalizer(f,g) == FinOrdFunction(Int[], 5)
@test equalizer([f,g]) == FinOrdFunction(Int[], 5)

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

# Pullback using generic limit interface
f,g = FinOrdFunction([1,1,3,2],4), FinOrdFunction([1,1,4,2],4)
cone = limit(Diagram([FinOrd(4),FinOrd(4),FinOrd(4)], [(1,3,f),(2,3,g)]))
@test apex(cone) == FinOrd(5)
@test force(leg(cone,1)) == FinOrdFunction([1,2,1,2,4],4)
@test force(leg(cone,2)) == FinOrdFunction([1,1,2,2,4],4)

# Colimits
##########

# Initial object.
@test initial(FinOrd) == FinOrd(0)

# Binary Coproduct.
cospan = coproduct(FinOrd(2), FinOrd(3))
@test base(cospan) == FinOrd(5)
@test left(cospan) == FinOrdFunction([1,2], 5)
@test right(cospan) == FinOrdFunction([3,4,5], 5)

# N-ary Coproduct.
cocone = coproduct([FinOrd(2), FinOrd(3)])
@test base(cocone) == FinOrd(5)
@test leg(cocone,1) == FinOrdFunction([1,2], 5)
@test leg(cocone,2) == FinOrdFunction([3,4,5], 5)
@test base(coproduct(FinOrd[])) == FinOrd(0)

# Coequalizer from a singleton set.
f, g = FinOrdFunction([1], 3), FinOrdFunction([3], 3)
@test coequalizer(f,g) == FinOrdFunction([1,2,1], 2)
@test coequalizer([f,g]) == FinOrdFunction([1,2,1], 2)

# Coequalizer in case of identical functions.
f = FinOrdFunction([4,2,3,1], 5)
@test coequalizer(f,f) == force(id(FinOrd(5)))
@test coequalizer([f,f]) == force(id(FinOrd(5)))

# Coequalizer identifying everything.
f, g = id(FinOrd(5)), FinOrdFunction([2,3,4,5,1], 5)
@test coequalizer(f,g) == FinOrdFunction(repeat([1],5))
@test coequalizer([f,g]) == FinOrdFunction(repeat([1],5))

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

# Same thing with generic colimit interface
diag = Diagram([FinOrd(1),FinOrd(2),FinOrd(3)],[(1,2,f), (1,3,g)])
cocone = colimit(diag)
@test base(cocone) == FinOrd(4)
h, k = leg(cocone,2), leg(cocone,3)
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

# Same thing with generic colimit interface
diag = Diagram([FinOrd(2),FinOrd(2),FinOrd(2)],[(1,2,f),(1,3,g)])
cocone = colimit(diag)
@test base(cocone) == FinOrd(2)
h,k = leg(cocone,2), leg(cocone,3)
@test compose(f,h) == compose(g,k)
@test h == FinOrdFunction([1,2], 2)
@test k == FinOrdFunction([1,1], 2)

end
