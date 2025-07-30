using Catlab, Test

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


# Terminal object.
I = terminal(FinSet{Int})
@test ob(I) == FinSet(1)
@test force(delete(I, FinSet(3))) == FinFunction([1,1,1])

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
for Alg in (NestedLoopJoin, SortMergeJoin, HashJoin)
  limt = pullback(f, g, alg=Alg())
  @test ob(limt) == FinSet(6)
  @test tuples(limt) == [(1,4), (2,2), (2,3), (3,2), (3,3), (5,5)]
end

# Ternary pullback using different algorithms.
f, g = FinDomFunction([:a,:b,:c]), FinDomFunction([:c,:b,:a])
h = FinDomFunction([:a,:a,:b,:b,:c,:c])
lim = limit(SMulticospan{3}(f, g, h), alg=ComposeProductEqualizer())
@test ob(lim) == FinSet(6)
reference_tuples = tuples(lim)

for Alg in (NestedLoopJoin, SortMergeJoin, HashJoin)
  limt = limit(SMulticospan{3}(f, g, h), alg=Alg())
  @test ob(limt) == FinSet(6)
  @test tuples(limt) == reference_tuples
end

# Pullback involving a constant, which should be handled specially.
lim = pullback(FinFunction([3], 4), FinFunction([1,3,4,2,3,3]), alg=SmartJoin())
@test ob(lim)== FinSet(3)
@test proj1(lim) == ConstantFunction(1, FinSet(3), FinSet(1))
@test proj2(lim) == FinFunction([2,5,6], 6)

# General limits
#---------------

# Pullback as limit of free diagram.
f, g = FinFunction([1,1,3,2],4), FinFunction([1,1,4,2],4)
lim = limit(FreeDiagram(Cospan(f, g)))
@test ob(lim) == FinSet(5)
π1, π2 = legs(lim)[1:2]
@test force(π1) == FinFunction([1,2,1,2,4], 4)
@test force(π2) == FinFunction([1,1,2,2,4], 4)

f′, g′ = FinFunction([1,2,4]), FinFunction([2,1,4])
h = universal(lim, Multispan([f′, g′, f′⋅f])) # f′⋅f == g′⋅g
@test force(h ⋅ π1) == f′
@test force(h ⋅ π2) == g′

# Pullback as limit of bipartite free diagram.
lim = limit(BipartiteFreeDiagram{SetOb,FinDomFunction{Int}}(Cospan(f, g)))
π1, π2 = legs(lim)
@test π1 == FinFunction([1,1,2,2,4], 4)
@test π2 == FinFunction([1,2,1,2,4], 4)
lim′ = limit(FreeDiagram{SetOb,FinDomFunction{Int}}(Cospan(f, g)),
             ToBipartiteLimit())
@test legs(lim′)[1:2] == legs(lim)

h = universal(lim, Span(f′, g′))
@test force(h ⋅ π1) == f′
@test force(h ⋅ π2) == g′
