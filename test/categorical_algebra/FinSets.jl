module TestFinSets
using Test

using Catlab.Theories, Catlab.CategoricalAlgebra
using Catlab.CategoricalAlgebra.Sets, Catlab.CategoricalAlgebra.FinSets

# Functions between finite sets
###############################

f = FinFunction([1,3,4], 5)
g = FinFunction([1,1,2,2,3], 3)
h = FinFunction([3,1,2], 3)
@test dom(f) == FinSet(3)
@test codom(f) == FinSet(5)
@test codom(FinFunction([1,3,4])) == FinSet(4)

# Evaluation.
rot3(x) = (x % 3) + 1
@test map(f, 1:3) == [1,3,4]
@test map(FinFunction(rot3, 3, 3), 1:3) == [2,3,1]
@test map(id(FinSet(3)), 1:3) == [1,2,3]

# Pretty-print.
@test sprint(show, FinSet(3)) == "FinSet(3)"
@test sprint(show, f) == "FinFunction($([1,3,4]), 3, 5)"
@test sprint(show, FinFunction(rot3, 3, 3)) ==
  "FinFunction(rot3, FinSet(3), FinSet(3))"
@test sprint(show, id(FinSet(3))) == "FinFunction(identity, FinSet(3))"

# Composition.
@test compose(f,g) == FinFunction([1,2,2], 3)
@test compose(g,h) == FinFunction([3,3,1,1,2], 3)
@test compose(compose(f,g),h) == compose(f,compose(g,h))
@test compose(id(dom(f)), f) == f
@test compose(f, id(codom(f))) == f

# Functions out of finite sets
##############################

k = FinDomFunction([:a,:b,:c,:d,:e])
@test dom(k) == FinSet(5)
@test codom(k) == TypeSet(Symbol)
@test k(3) == :c
@test collect(k) == [:a,:b,:c,:d,:e]
@test sprint(show, k) ==
  "FinDomFunction($([:a,:b,:c,:d,:e]), FinSet(5), TypeSet(Symbol))"

f = FinFunction([1,3,4], 5)
@test compose(f,k) == FinDomFunction([:a,:c,:d])

# Indexed functions
###################

@test !is_indexed(FinFunction([1,3,2]))
@test !is_indexed(FinDomFunction([:a,:c,:b]))

# Indexed functions between finite sets.
f = IndexedFinFunction([1,2,1,3], 5)
@test is_indexed(f)
@test force(f) === f
@test (dom(f), codom(f)) == (FinSet(4), FinSet(5))
@test f(1) == 1
@test preimage(f, 1) == [1,3]
@test preimage(f, 3) == [4]
@test isempty(preimage(f, 4))

g = FinFunction(5:-1:1)
@test compose(f,g) == FinFunction([5,4,5,3])

@test is_indexed(id(FinSet(3)))
@test preimage(id(FinSet(3)), 2) == [2]

# Indexed functions out of finite sets.
k = IndexedFinDomFunction([:a,:b,:a,:c])
@test is_indexed(k)
@test (dom(k), codom(k)) == (FinSet(4), TypeSet(Symbol))
@test k(1) == :a
@test preimage(k, :a) == [1,3]
@test preimage(k, :c) == [4]
@test isempty(preimage(k, :d))

f = FinFunction([1,3,2], 4)
@test compose(f,k) == FinDomFunction([:a,:a,:b])

# Limits
########

# Terminal object
#----------------

@test ob(terminal(FinSet{Int})) == FinSet(1)
@test delete(terminal(FinSet{Int}), FinSet(3)) == FinFunction([1,1,1])

# Products
#---------

# Binary product.
lim = product(FinSet(2), FinSet(3))
@test ob(lim) == FinSet(6)
@test force(proj1(lim)) == FinFunction([1,2,1,2,1,2])
@test force(proj2(lim)) == FinFunction([1,1,2,2,3,3])

lim = product(FinSet(4), FinSet(3))
f, g = FinFunction([2,1,4]), FinFunction([1,3,2])
@test force(pair(lim,f,g) ⋅ proj1(lim)) == f
@test force(pair(lim,f,g) ⋅ proj2(lim)) == g

# N-ary product.
lim = product([FinSet(2), FinSet(3)])
@test ob(lim) == FinSet(6)
@test force.(legs(lim)) ==
  [FinFunction([1,2,1,2,1,2]), FinFunction([1,1,2,2,3,3])]
@test ob(product(FinSet{Int}[])) == FinSet(1)

lim = product([FinSet(4), FinSet(3)])
@test force(pair(lim,[f,g]) ⋅ first(legs(lim))) == f
@test force(pair(lim,[f,g]) ⋅ last(legs(lim))) == g

# Equalizers
#-----------

f, g = FinFunction([1,2,4,3]), FinFunction([3,2,4,1])
eq = equalizer(f,g)
@test incl(eq) == FinFunction([2,3], 4)
@test incl(equalizer([f,g])) == incl(eq)
@test factorize(eq, FinFunction([2,3,2])) == FinFunction([1,2,1])

# Equalizer of identical functions.
f = FinFunction([4,2,3,1], 5)
eq = equalizer(f,f)
@test incl(eq) == force(id(FinSet(4)))
@test incl(equalizer([f,f])) == incl(eq)
@test factorize(eq, FinFunction([2,1,3,3])) == FinFunction([2,1,3,3], 4)

# Equalizer matching nothing.
f, g = id(FinSet(5)), FinFunction([2,3,4,5,1], 5)
eq = equalizer(f,g)
@test incl(eq) == FinFunction(Int[], 5)
@test incl(equalizer([f,g])) == incl(eq)
@test factorize(eq, FinFunction(Int[])) == FinFunction(Int[])

# Equalizer of functions into non-finite set.
f = FinDomFunction([:a, :b, :d, :c])
g = FinDomFunction([:c, :b, :d, :a])
eq = equalizer(f,g)
@test incl(eq) == FinFunction([2,3], 4)

# Pullbacks
#----------

lim = pullback(FinFunction([1,1,3,2],4), FinFunction([1,1,4,2],4))
@test ob(lim) == FinSet(5)
@test force(proj1(lim)) == FinFunction([1,2,1,2,4], 4)
@test force(proj2(lim)) == FinFunction([1,1,2,2,4], 4)

f, g = FinFunction([1,2,4]), FinFunction([2,1,4])
@test force(pair(lim,f,g) ⋅ proj1(lim)) == f
@test force(pair(lim,f,g) ⋅ proj2(lim)) == g

# Pullback from a singleton set: the degenerate case of a product.
lim = pullback(FinFunction([1,1]), FinFunction([1,1,1]))
@test ob(lim) == FinSet(6)
@test force(proj1(lim)) == FinFunction([1,2,1,2,1,2])
@test force(proj2(lim)) == FinFunction([1,1,2,2,3,3])

f, g = FinFunction([1,1,2]), FinFunction([3,2,1])
@test force(pair(lim,f,g) ⋅ proj1(lim)) == f
@test force(pair(lim,f,g) ⋅ proj2(lim)) == g

# Pullback of a cospan into non-finite set.
f = FinDomFunction([:a, :a, :c, :b])
g = FinDomFunction([:a, :a, :d, :b])
π1, π2 = lim = pullback(f, g)
@test ob(lim) == FinSet(5)
@test force(π1) == FinFunction([1,2,1,2,4], 4)
@test force(π2) == FinFunction([1,1,2,2,4], 4)

# Pullback using different algorithms.
tuples(lim::AbstractLimit) =
  sort!([ Tuple(map(π -> π(i), legs(lim))) for i in ob(lim) ])

f, g = FinFunction([3,1,1,5,2],5), FinFunction([4,1,1,3,2],5)
lim = pullback(f, g, alg=NestedLoopJoin())
@test ob(lim) == FinSet(6)
@test tuples(lim) == [(1,4), (2,2), (2,3), (3,2), (3,3), (5,5)]

lim = pullback(f, g, alg=SortMergeJoin())
@test ob(lim) == FinSet(6)
@test tuples(lim) == [(1,4), (2,2), (2,3), (3,2), (3,3), (5,5)]

# General limits
#---------------

# Pullback as a general limit.
f, g = FinFunction([1,1,3,2],4), FinFunction([1,1,4,2],4)
lim = limit(FreeDiagram([FinSet(4),FinSet(4),FinSet(4)], [(f,1,3),(g,2,3)]))
@test ob(lim) == FinSet(5)
π1, π2 = legs(lim)[1:2]
@test force(π1) == FinFunction([1,2,1,2,4], 4)
@test force(π2) == FinFunction([1,1,2,2,4], 4)

f′, g′ = FinFunction([1,2,4]), FinFunction([2,1,4])
h = universal(lim, Multispan([f′, g′, f′⋅f])) # f′⋅f == g′⋅g
@test force(h ⋅ π1) == f′
@test force(h ⋅ π2) == g′

# Colimits
##########

# Initial object
#---------------

@test ob(initial(FinSet{Int})) == FinSet(0)
@test create(initial(FinSet{Int}), FinSet(3)) == FinFunction(Int[], 3)

# Coproducts
#-----------

# Binary coproduct.
colim = coproduct(FinSet(2), FinSet(3))
@test ob(colim) == FinSet(5)
@test coproj1(colim) == FinFunction([1,2], 5)
@test coproj2(colim) == FinFunction([3,4,5], 5)

f, g = FinFunction([3,5], 5), FinFunction([1,2,3], 5)
@test force(coproj1(colim) ⋅ copair(colim,f,g)) == f
@test force(coproj2(colim) ⋅ copair(colim,f,g)) == g

# N-ary coproduct.
colim = coproduct([FinSet(2), FinSet(3)])
@test ob(colim) == FinSet(5)
@test legs(colim) == [FinFunction([1,2], 5), FinFunction([3,4,5], 5)]
@test ob(coproduct(FinSet{Int}[])) == FinSet(0)

@test force(first(legs(colim)) ⋅ copair(colim,[f,g])) == f
@test force(last(legs(colim)) ⋅ copair(colim,[f,g])) == g

# Coequalizers
#-------------

# Coequalizer from a singleton set.
f, g = FinFunction([1], 3), FinFunction([3], 3)
coeq = coequalizer(f,g)
@test proj(coeq) == FinFunction([1,2,1], 2)
@test proj(coequalizer([f,g])) == proj(coeq)
@test factorize(coeq, FinFunction([4,1,4])) == FinFunction([4,1])
@test_throws AssertionError factorize(coeq, FinFunction([3,1,4]))

# Coequalizer in case of identical functions.
f = FinFunction([4,2,3,1], 5)
coeq = coequalizer(f,f)
@test proj(coeq) == force(id(FinSet(5)))
@test proj(coequalizer([f,f])) == proj(coeq)
@test factorize(coeq, FinFunction([2,1,3,3,4])) == FinFunction([2,1,3,3,4])

# Coequalizer identifying everything.
f, g = id(FinSet(5)), FinFunction([2,3,4,5,1], 5)
coeq = coequalizer(f,g)
@test proj(coeq) == FinFunction(fill(1,5))
@test proj(coequalizer([f,g])) == proj(coeq)
@test factorize(coeq, FinFunction(fill(3,5))) == FinFunction([3])

# Pushouts
#---------

# Pushout from the empty set: the degenerate case of the coproduct.
f, g = FinFunction(Int[], 2), FinFunction(Int[], 3)
colim = pushout(f,g)
@test ob(colim) == FinSet(5)
@test coproj1(colim) == FinFunction([1,2], 5)
@test coproj2(colim) == FinFunction([3,4,5], 5)

h, k = FinFunction([3,5], 5), FinFunction([1,2,3], 5)
@test force(coproj1(colim) ⋅ copair(colim,h,k)) == h
@test force(coproj2(colim) ⋅ copair(colim,h,k)) == k

# Pushout from a singleton set.
f, g = FinFunction([1], 2), FinFunction([2], 3)
colim = pushout(f,g)
@test ob(colim) == FinSet(4)
ι1, ι2 = colim
@test compose(f,ι1) == compose(g,ι2)
@test ι1 == FinFunction([1,2], 4)
@test ι2 == FinFunction([3,1,4], 4)

h, k = FinFunction([3,5]), FinFunction([1,3,5])
@test force(coproj1(colim) ⋅ copair(colim,h,k)) == h
@test force(coproj2(colim) ⋅ copair(colim,h,k)) == k
k = FinFunction([1,2,5])
@test_throws AssertionError copair(colim,h,k)

# Same thing with generic colimit interface
diagram = FreeDiagram([FinSet(1),FinSet(2),FinSet(3)],[(f,1,2), (g,1,3)])
colim = colimit(diagram)
@test ob(colim) == FinSet(4)
_, ι1, ι2 = colim
@test compose(f,ι1) == compose(g,ι2)
@test ι1 == FinFunction([1,2], 4)
@test ι2 == FinFunction([3,1,4], 4)

h, k = FinFunction([3,5]), FinFunction([1,3,5])
ℓ = universal(colim, Multicospan([f⋅h, h, k])) # f⋅h == g⋅k
@test force(ι1 ⋅ ℓ) == h
@test force(ι2 ⋅ ℓ) == k

# Pushout from a two-element set, with non-injective legs.
f, g = FinFunction([1,1], 2), FinFunction([1,2], 2)
colim = pushout(f,g)
@test ob(colim) == FinSet(2)
ι1, ι2 = colim
@test compose(f,ι1) == compose(g,ι2)
@test ι1 == FinFunction([1,2], 2)
@test ι2 == FinFunction([1,1], 2)

# Same thing with generic colimit interface
diagram = FreeDiagram([FinSet(2),FinSet(2),FinSet(2)],[(f,1,2),(g,1,3)])
colim = colimit(diagram)
@test ob(colim) == FinSet(2)
_, ι1, ι2 = colim
@test compose(f,ι1) == compose(g,ι2)
@test ι1 == FinFunction([1,2], 2)
@test ι2 == FinFunction([1,1], 2)

end
