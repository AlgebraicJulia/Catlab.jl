module TestFinSets
using Test

using Catlab.Theories
using Catlab.CategoricalAlgebra.ShapeDiagrams, Catlab.CategoricalAlgebra.FinSets

# Category of finite ordinals
#############################

f = FinSetFunction([1,3,4], 5)
g = FinSetFunction([1,1,2,2,3], 3)
h = FinSetFunction([3,1,2], 3)

# Evaluation.
@test map(f, 1:3) == [1,3,4]
@test map(id(FinSet(3)), 1:3) == [1,2,3]
@test map(FinSetFunction(x -> (x % 3) + 1, 3, 3), 1:3) == [2,3,1]

# Composition and identities.
@test dom(f) == FinSet(3)
@test codom(f) == FinSet(5)
@test compose(f,g) == FinSetFunction([1,2,2], 3)
@test compose(g,h) == FinSetFunction([3,3,1,1,2], 3)
@test compose(compose(f,g),h) == compose(f,compose(g,h))
@test force(compose(id(dom(f)),f)) == f
@test force(compose(f,id(codom(f)))) == f

# Limits
########

# Terminal object.
@test terminal(FinSet{Int}) == FinSet(1)

# Binary Product.
span = product(FinSet(2), FinSet(3))
@test apex(span) == FinSet(6)
@test force(left(span)) == FinSetFunction([1,2,1,2,1,2])
@test force(right(span)) == FinSetFunction([1,1,2,2,3,3])

# N-ary Product.
cone = product([FinSet(2), FinSet(3)])
@test apex(cone) == FinSet(6)
@test force(leg(cone,1)) == FinSetFunction([1,2,1,2,1,2])
@test force(leg(cone,2)) == FinSetFunction([1,1,2,2,3,3])
@test apex(product(FinSet{Int}[])) == FinSet(1)

# Equalizer.
f, g = FinSetFunction([1,2,3]), FinSetFunction([3,2,1])
@test equalizer(f,g) == FinSetFunction([2], 3)
@test equalizer([f,g]) == FinSetFunction([2], 3)

# Equalizer in case of identical functions.
f = FinSetFunction([4,2,3,1], 5)
@test equalizer(f,f) == force(id(FinSet(4)))
@test equalizer([f,f]) == force(id(FinSet(4)))

# Equalizer matching nothing.
f, g = id(FinSet(5)), FinSetFunction([2,3,4,5,1], 5)
@test equalizer(f,g) == FinSetFunction(Int[], 5)
@test equalizer([f,g]) == FinSetFunction(Int[], 5)

# Pullback.
span = pullback(Cospan(FinSetFunction([1,1,3,2],4), FinSetFunction([1,1,4,2],4)))
@test apex(span) == FinSet(5)
@test force(left(span)) == FinSetFunction([1,2,1,2,4], 4)
@test force(right(span)) == FinSetFunction([1,1,2,2,4], 4)

# Pullback from a singleton set: the degenerate case of a product.
span = pullback(Cospan(FinSetFunction([1,1]), FinSetFunction([1,1,1])))
@test apex(span) == FinSet(6)
@test force(left(span)) == FinSetFunction([1,2,1,2,1,2])
@test force(right(span)) == FinSetFunction([1,1,2,2,3,3])

# Pullback using generic limit interface
f,g = FinSetFunction([1,1,3,2],4), FinSetFunction([1,1,4,2],4)
cone = limit(Diagram([FinSet(4),FinSet(4),FinSet(4)], [(1,3,f),(2,3,g)]))
@test apex(cone) == FinSet(5)
@test force(leg(cone,1)) == FinSetFunction([1,2,1,2,4],4)
@test force(leg(cone,2)) == FinSetFunction([1,1,2,2,4],4)

# Colimits
##########

# Initial object.
@test initial(FinSet{Int}) == FinSet(0)

# Binary Coproduct.
cospan = coproduct(FinSet(2), FinSet(3))
@test base(cospan) == FinSet(5)
@test left(cospan) == FinSetFunction([1,2], 5)
@test right(cospan) == FinSetFunction([3,4,5], 5)

# N-ary Coproduct.
cocone = coproduct([FinSet(2), FinSet(3)])
@test base(cocone) == FinSet(5)
@test leg(cocone,1) == FinSetFunction([1,2], 5)
@test leg(cocone,2) == FinSetFunction([3,4,5], 5)
@test base(coproduct(FinSet{Int}[])) == FinSet(0)

# Coequalizer from a singleton set.
f, g = FinSetFunction([1], 3), FinSetFunction([3], 3)
@test coequalizer(f,g) == FinSetFunction([1,2,1], 2)
@test coequalizer([f,g]) == FinSetFunction([1,2,1], 2)

# Coequalizer in case of identical functions.
f = FinSetFunction([4,2,3,1], 5)
@test coequalizer(f,f) == force(id(FinSet(5)))
@test coequalizer([f,f]) == force(id(FinSet(5)))

# Coequalizer identifying everything.
f, g = id(FinSet(5)), FinSetFunction([2,3,4,5,1], 5)
@test coequalizer(f,g) == FinSetFunction(repeat([1],5))
@test coequalizer([f,g]) == FinSetFunction(repeat([1],5))

# Pushout from the empty set: the degenerate case of the coproduct.
f, g = FinSetFunction(Int[], 2), FinSetFunction(Int[], 3)
cospan = pushout(Span(f,g))
@test base(cospan) == FinSet(5)
@test left(cospan) == FinSetFunction([1,2], 5)
@test right(cospan) == FinSetFunction([3,4,5], 5)

# Pushout from a singleton set.
f, g = FinSetFunction([1], 2), FinSetFunction([2], 3)
cospan = pushout(Span(f,g))
@test base(cospan) == FinSet(4)
h, k = left(cospan), right(cospan)
@test compose(f,h) == compose(g,k)
@test h == FinSetFunction([1,2], 4)
@test k == FinSetFunction([3,1,4], 4)

# Same thing with generic colimit interface
diag = Diagram([FinSet(1),FinSet(2),FinSet(3)],[(1,2,f), (1,3,g)])
cocone = colimit(diag)
@test base(cocone) == FinSet(4)
h, k = leg(cocone,2), leg(cocone,3)
@test compose(f,h) == compose(g,k)
@test h == FinSetFunction([1,2], 4)
@test k == FinSetFunction([3,1,4], 4)

# Pushout from a two-element set, with non-injective legs.
f, g = FinSetFunction([1,1], 2), FinSetFunction([1,2], 2)
cospan = pushout(Span(f,g))
@test base(cospan) == FinSet(2)
h, k = left(cospan), right(cospan)
@test compose(f,h) == compose(g,k)
@test h == FinSetFunction([1,2], 2)
@test k == FinSetFunction([1,1], 2)

# Same thing with generic colimit interface
diag = Diagram([FinSet(2),FinSet(2),FinSet(2)],[(1,2,f),(1,3,g)])
cocone = colimit(diag)
@test base(cocone) == FinSet(2)
h,k = leg(cocone,2), leg(cocone,3)
@test compose(f,h) == compose(g,k)
@test h == FinSetFunction([1,2], 2)
@test k == FinSetFunction([1,1], 2)

end
