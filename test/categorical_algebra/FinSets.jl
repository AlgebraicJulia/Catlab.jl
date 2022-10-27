module TestFinSets
using Test

using Catlab.Theories, Catlab.CategoricalAlgebra

sshow(args...) = sprint(show, args...)

# Finite sets
#############

set = FinSet(3)
@test length(set) == 3
@test collect(set) == 1:3
@test 2 ∈ set && 10 ∉ set
@test sshow(set) == "FinSet(3)"

# Collections as sets.
set = FinSet(Set(1:2:5))
@test length(set) == 3
@test sort!(collect(set)) == [1,3,5]
@test 3 ∈ set && 4 ∉ set
@test startswith(sshow(set), "FinSet(Set(")

# Tables as sets.
set = FinSet((x=[1,3,5], y=["a","b","c"]))
@test eltype(set) == NamedTuple{(:x,:y),Tuple{Int,String}}
@test length(set) == 3
@test collect(set) == [(x=1, y="a"), (x=3, y="b"), (x=5, y="c")]
@test startswith(sshow(set), "TabularSet(")
@test startswith(sshow(MIME("text/plain"), set), "3-element TabularSet")
@test startswith(sshow(MIME("text/html"), set), "<div")

# Discrete categories.
C = FinCat(FinSet(3))
@test C isa FinCat{Int,Int}
@test is_discrete(C)
@test collect(ob_generators(C)) == 1:3
@test isempty(hom_generators(C))
@test (dom(C, 1), codom(C, 1)) == (1, 1)
@test (id(C, 2), compose(C, 2, 2)) == (2, 2)
@test sshow(C) == "FinCat(3)"

F = FinDomFunctor([FinSet(1), FinSet(3), FinSet(1)],
                  C, TypeCat(FinSet{Int}, FinFunction{Int}))
@test ob_map(F, 2) == FinSet(3)
@test hom_map(F, 2) == id(FinSet(3))

# Functions between finite sets
###############################

f = FinFunction([1,3,4], 5)
g = FinFunction([1,1,2,2,3], 3)
h = FinFunction([3,1,2], 3)
@test f isa FinFunction{Int,Int}
@test (dom(f), codom(f)) == (FinSet(3), FinSet(5))
@test force(f) === f
@test codom(FinFunction([1,3,4])) == FinSet(4)

X = FinSet(Set([:w,:x,:y,:z]))
k = FinFunction(Dict(:a => :x, :b => :y, :c => :z), X)
ℓ = FinFunction(Dict(:w => 2, :x => 1, :y => 1, :z => 4), FinSet(4))
@test ℓ isa FinFunction{<:AbstractSet{Symbol},Int}
@test (dom(k), codom(k)) == (FinSet(Set([:a, :b, :c])), X)
@test (dom(ℓ), codom(ℓ)) == (X, FinSet(4))
@test force(k) === k
@test codom(FinFunction(Dict(:a => :x, :b => :y, :c => :z))) ==
  FinSet(Set([:x,:y,:z]))

# Evaluation.
rot3(x) = (x % 3) + 1
@test map(f, 1:3) == [1,3,4]
@test map(k, [:a,:b,:c]) == [:x,:y,:z]
@test map(FinFunction(rot3, 3, 3), 1:3) == [2,3,1]
@test map(id(FinSet(3)), 1:3) == [1,2,3]

# Composition.
@test compose(f,g) == FinFunction([1,2,2], 3)
@test compose(g,h) == FinFunction([3,3,1,1,2], 3)
@test compose(k,ℓ) == FinFunction(Dict(:a => 1, :b => 1, :c => 4), FinSet(4))
@test compose(compose(f,g),h) == compose(f,compose(g,h))
@test compose(id(dom(f)), f) == f
@test compose(f, id(codom(f))) == f

# Indexing.
@test !is_indexed(f)
@test is_indexed(id(FinSet(3)))
@test preimage(id(FinSet(3)), 2) == [2]

f = FinFunction([1,2,1,3], 5, index=true)
@test is_indexed(f)
@test force(f) === f
@test (dom(f), codom(f)) == (FinSet(4), FinSet(5))
@test f(1) == 1
@test preimage(f, 1) == [1,3]
@test preimage(f, 3) == [4]
@test isempty(preimage(f, 4))

g = FinFunction(5:-1:1)
@test compose(f,g) == FinFunction([5,4,5,3])

# Pretty-print.
@test sshow(FinFunction(rot3, 3, 3)) ==
  "FinFunction(rot3, FinSet(3), FinSet(3))"
@test sshow(id(FinSet(3))) == "id(FinSet(3))"
@test sshow(FinFunction([1,3,4], 5)) == "FinFunction($([1,3,4]), 3, 5)"
@test sshow(FinFunction([1,3,4], 5, index=true)) ==
  "FinFunction($([1,3,4]), 3, 5, index=true)"
@test sshow(FinFunction(Dict(:a => 1, :b => 3), FinSet(3))) ==
  "FinFunction($(Dict(:a => 1, :b => 3)), FinSet(3))"

# Injectivity / Surjectivity.
f = FinFunction([1,3,4])
g = FinFunction([1,1,2])
X = FinSet(Set([:x,:y,:z]))
k = FinFunction(Dict(:a => :x, :b => :y, :c => :z), X)

@test is_monic(f)
@test !is_epic(f)
@test is_epic(g)
@test !is_monic(g)
@test is_monic(k)
@test is_epic(k)

# Functions out of finite sets
##############################

k = FinDomFunction([:a,:b,:c,:d,:e])
@test (dom(k), codom(k)) == (FinSet(5), TypeSet(Symbol))
@test k(3) == :c
@test collect(k) == [:a,:b,:c,:d,:e]
@test sshow(k) ==
  "FinDomFunction($([:a,:b,:c,:d,:e]), FinSet(5), TypeSet(Symbol))"

f = FinFunction([1,3,4], 5)
@test compose(f,k) == FinDomFunction([:a,:c,:d])

# Indexing.
@test !is_indexed(k)
@test preimage(k, :c) == [3]

k = FinDomFunction(5:10)
@test is_indexed(k)
@test preimage(k, 6) == [2]
@test isempty(preimage(k, 4))

k = FinDomFunction([:a,:b,:a,:c], index=true)
@test is_indexed(k)
@test (dom(k), codom(k)) == (FinSet(4), TypeSet(Symbol))
@test k(1) == :a
@test preimage(k, :a) == [1,3]
@test preimage(k, :c) == [4]
@test isempty(preimage(k, :d))
@test sshow(k) ==
  "FinDomFunction($([:a,:b,:a,:c]), FinSet(4), TypeSet(Symbol), index=true)"

f = FinFunction([1,3,2], 4)
@test compose(f,k) == FinDomFunction([:a,:a,:b])

# Limits
########

# Products
#---------

# Terminal object.
I = terminal(FinSet{Int})
@test ob(I) == FinSet(1)
@test force(delete(I, FinSet(3))) == FinFunction([1,1,1])

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
for Alg in (NestedLoopJoin, SortMergeJoin, HashJoin)
  lim = pullback(f, g, alg=Alg())
  @test ob(lim) == FinSet(6)
  @test tuples(lim) == [(1,4), (2,2), (2,3), (3,2), (3,3), (5,5)]
end

# Ternary pullback using different algorithms.
f, g = FinDomFunction([:a,:b,:c]), FinDomFunction([:c,:b,:a])
h = FinDomFunction([:a,:a,:b,:b,:c,:c])
lim = limit(SMulticospan{3}(f, g, h), alg=ComposeProductEqualizer())
@test ob(lim) == FinSet(6)
reference_tuples = tuples(lim)

for Alg in (NestedLoopJoin, SortMergeJoin, HashJoin)
  lim = limit(SMulticospan{3}(f, g, h), alg=Alg())
  @test ob(lim) == FinSet(6)
  @test tuples(lim) == reference_tuples
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

# Equalizer as limit of bipartite free diagram.
f, g = [FinDomFunction(x -> x % i, FinSet(100), TypeSet(Int)) for i in 2:3]
d = BipartiteFreeDiagram{SetOb,FinDomFunction{Int}}(ParallelPair(f, g))
lim = (ι,) = limit(d)
@test ι == incl(equalizer(f, g))

# Two pullbacks, which should be reduced to a single pullback by pairing.
f1, g1 = FinDomFunction([1,1,2,2,3,3]), FinDomFunction([:a,:a,:a,:b,:b,:b])
f2, g2 = FinDomFunction([1,2,3]), FinDomFunction([:a,:b,:c])
d = BipartiteFreeDiagram{SetOb,FinDomFunction{Int}}(2, 2)
d[:ob₁], d[:ob₂] = [FinSet(6), FinSet(3)], [TypeSet(Int), TypeSet(Symbol)]
add_edges!(d, [1,1,2,2], [1,2,1,2], hom=[f1,g1,f2,g2])
lim = π1, π2 = limit(d)
@test π1 == FinFunction([1,2,4], 6)
@test π2 == FinFunction([1,1,2], 3)

# Colimits
##########

# Coproducts
#-----------

# Initial object.
@test ob(initial(FinSet{Int})) == FinSet(0)
@test create(initial(FinSet{Int}), FinSet(3)) == FinFunction(Int[], 3)

# Binary coproduct.
colim = coproduct(FinSet(2), FinSet(3))
@test ob(colim) == FinSet(5)
@test coproj1(colim) == FinFunction([1,2], 5)
@test coproj2(colim) == FinFunction([3,4,5], 5)

f, g = FinFunction([3,5], 5), FinFunction([1,2,3], 5)
h = copair(colim, f, g)
@test force(coproj1(colim) ⋅ h) == f
@test force(coproj2(colim) ⋅ h) == g

# N-ary coproduct.
colim = coproduct([FinSet(2), FinSet(3)])
@test ob(colim) == FinSet(5)
@test legs(colim) == [FinFunction([1,2], 5), FinFunction([3,4,5], 5)]
@test ob(coproduct(FinSet{Int}[])) == FinSet(0)

h = copair(colim, [f,g])
@test force(first(legs(colim)) ⋅ h) == f
@test force(last(legs(colim)) ⋅ h) == g

# Cocartesian monoidal structure.
@test FinSet(2)⊕FinSet(3) == FinSet(5)
@test oplus([FinSet(2), FinSet(3), FinSet(4)]) == FinSet(9)
@test f⊕g == FinFunction([3,5,6,7,8], 10)
@test mzero(FinSet{Int}) == FinSet(0)
@test swap(FinSet(2), FinSet(3)) == FinFunction([4,5,1,2,3])
ι1, ι2 = coproj1(FinSet(2),FinSet(3)), coproj2(FinSet(2),FinSet(3))
@test ι1 == FinFunction([1,2], 5)
@test ι2 == FinFunction([3,4,5], 5)

# Coequalizers
#-------------

# Coequalizer from a singleton set.
f, g = FinFunction([1], 3), FinFunction([3], 3)
coeq = coequalizer(f,g)
@test proj(coeq) == FinFunction([1,2,1], 2)
@test proj(coequalizer([f,g])) == proj(coeq)
@test factorize(coeq, FinFunction([4,1,4])) == FinFunction([4,1])
@test_throws ErrorException factorize(coeq, FinFunction([3,1,4]))

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
ℓ = copair(colim, h, k)
@test force(coproj1(colim) ⋅ ℓ) == h
@test force(coproj2(colim) ⋅ ℓ) == k

# Pushout from a singleton set.
f, g = FinFunction([1], 2), FinFunction([2], 3)
colim = pushout(f,g)
@test ob(colim) == FinSet(4)
ι1, ι2 = colim
@test compose(f,ι1) == compose(g,ι2)
@test ι1 == FinFunction([1,2], 4)
@test ι2 == FinFunction([3,1,4], 4)

h, k = FinFunction([3,5]), FinFunction([1,3,5])
ℓ = copair(colim, h, k)
@test force(coproj1(colim) ⋅ ℓ) == h
@test force(coproj2(colim) ⋅ ℓ) == k
k = FinFunction([1,2,5])
@test_throws ErrorException copair(colim,h,k)

h, k = FinDomFunction([:b,:c]), FinDomFunction([:a,:b,:c])
ℓ = copair(colim, h, k)
@test force(coproj1(colim) ⋅ ℓ) == h
@test force(coproj2(colim) ⋅ ℓ) == k
k = FinDomFunction([:a,:d,:c])
@test_throws ErrorException copair(colim,h,k)

# Same thing as a colimit of a general free diagram.
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
f, g = FinFunction([1,1], 2), FinFunction([1,2], 3)
colim = pushout(f,g)
@test ob(colim) == FinSet(3)
ι1, ι2 = colim
@test compose(f,ι1) == compose(g,ι2)
@test ι1 == FinFunction([1,2], 3)
@test ι2 == FinFunction([1,1,3], 3)

# Same thing as a colimit of a general free diagram.
diagram = FreeDiagram([FinSet(2),FinSet(2),FinSet(3)],[(f,1,2),(g,1,3)])
colim = colimit(diagram)
@test ob(colim) == FinSet(3)
_, ι1, ι2 = colim
@test ι1 == FinFunction([1,2], 3)
@test ι2 == FinFunction([1,1,3], 3)

# Same thing as a colimit of a bipartite free diagram.
bdiagram = BipartiteFreeDiagram([FinSet(2)], [FinSet(2),FinSet(3)],
                                [(f,1,1),(g,1,2)])
colim = colimit(bdiagram)
@test ob(colim) == FinSet(3)
ι1, ι2 = colim
@test ι1 == FinFunction([1,2], 3)
@test ι2 == FinFunction([1,1,3], 3)
colim′ = colimit(diagram, ToBipartiteColimit())
@test legs(colim′)[2:3] == legs(colim)

# Colimits with names
#--------------------

# Pushout with names.
A, B = FinSet([:w, :x, :y1]), FinSet([:x, :y2, :z])
f, g = FinFunction(Dict(:y => :y1), A), FinFunction(Dict(:y => :y2), B)
colim = pushout(f, g)
C = ob(colim)
@test Set(C) == Set([:w, Symbol("x#1"), Symbol("x#2"), :y, :z])
ι1, ι2 = colim
@test ι1 == FinFunction(Dict(:w => :w, :x => Symbol("x#1"), :y1 => :y), C)
@test ι2 == FinFunction(Dict(:x => Symbol("x#2"), :y2 => :y, :z => :z), C)

# Subsets
#########

X = FinSet(10)
A, B = SubFinSet(X, [1,2,5,6,8,9]), SubFinSet(X, [2,3,5,7,8])
@test ob(A) == X
A_pred = SubFinSet(Bool[1,1,0,0,1,1,0,1,1,0])
@test hom(A) == hom(A_pred)
@test FinSets.predicate(A) == FinSets.predicate(A_pred)

# Lattice of subsets.
@test A ∧ B |> force == SubFinSet(X, [2,5,8])
@test A ∨ B |> force == SubFinSet(X, [1,2,3,5,6,7,8,9])
@test ⊤(X) |> force == SubFinSet(X, 1:10)
@test ⊥(X) |> force == SubFinSet(X, 1:0)

for alg in (SubOpBoolean(), SubOpWithLimits())
  @test meet(A, B, alg) |> sort == SubFinSet(X, [2,5,8])
  @test join(A, B, alg) |> sort == SubFinSet(X, [1,2,3,5,6,7,8,9])
  @test top(X, alg) |> force == SubFinSet(X, 1:10)
  @test bottom(X, alg) |> force == SubFinSet(X, 1:0)
end

end
