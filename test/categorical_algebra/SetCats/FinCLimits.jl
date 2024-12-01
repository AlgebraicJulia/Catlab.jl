module TestSetCLimits 

using Test, Catlab, GATlab
using .ThCategory

const C = Category(TypeCat(SetC()))

# Initial/terminal objects
###########################

expected = Colimit(Diagram(C), Multicospan(FinSet(), FinFunction[]))
@test expected == initial(C)
@test apex(initial(C)) == FinSet()

@test create(FinSet(4), C) == FinFunction(Int[], FinSet(4))

expected = Limit(Diagram(C), Multispan(FinSet(1), FinFunction[]))
@test expected == terminal(C)
@test apex(terminal(C)) == FinSet(1)

@test delete(FinSet(2), C) |> collect == FinFunction([1,1], 1) |> collect


# Products
#-------------
xdiag = DiscreteDiagram(FinSet.([2,2]))
fs = FinFunction.([[1,2,1,2],[1,1,2,2]], 2)
expected = Limit(Diagram(xdiag, C), Span(fs...))
@test expected == product(FinSet.([2,2]), C)

sp = Span(FinFunction.([[1,2,2],[1,2,1]], 2)...)
@test universal(expected, sp; check=true).impl.val == [1,4,2]

# Error if pass in a span which doesn't have (2,2) as its feet.
sp = Span(fill(FinFunction(Int[], 3), 2)...)
@test_throws ErrorException universal(expected, sp; check=true)


lim = product([FinSet(2), FinSet(3)], C)
@test ob(lim) == FinSet(6)
@test force(proj1(lim)) == FinFunction([1,2,1,2,1,2], 2)
@test force(proj2(lim)) == FinFunction([1,1,2,2,3,3], 3)

lim = product([FinSet(4), FinSet(3)], C)
f, g = FinFunction([2,1,4], 4), FinFunction([1,3,2], 3)
@test force(compose(C, pair(lim,f,g), proj1(lim))) == f
@test force(compose(C, pair(lim,f,g), proj2(lim))) == g


# Coproducts
#-----------
fs = FinFunction.([[1,2],[3,4]], 4)
expected = Colimit(Diagram(xdiag, C), Cospan(fs...)) 
@test expected == coproduct(FinSet.([2,2]), C)

sp = Cospan(FinFunction.([[2,3],[1,4]], 4)...)
@test universal(expected, sp; check=true).impl.val == [2,3,1,4]


using .ThCocartesianCategory # Cocartesian monoidal structure.

CM = CocartesianMonoidal(C)
@withmodel CM (⊕, oplus, mzero, swap, coproj1, coproj2) begin 
  @test FinSet(2)⊕FinSet(3) == FinSet(5)
  @test oplus(FinSet.([2,3,4])) == FinSet(9)
  f, g = FinFunction([3,5], 5), FinFunction([1,2,3], 5)
  @test force(f ⊕ g) == FinFunction([3,5,6,7,8], 10)
  @test mzero() == FinSet(0)
  f_2_3 = FinSet.([2,3])
  @test swap(f_2_3...) == FinFunction([4,5,1,2,3], 5)
  ι1, ι2 = coproj1(f_2_3...), coproj2(f_2_3...)
  @test ι1 == FinFunction([1,2], 5)
  @test ι2 == FinFunction([3,4,5], 5)  
end


# Equalizers 
############

f, g = FinFunction.([[1,2,4,3], [3,2,4,1]], 4)
eq = equalizer([f,g], C)
@test incl(eq) == FinFunction([2,3], 4)
@test factorize(eq, FinFunction([2,3,2], 3)) == FinFunction([1,2,1], 2)

# Equalizer of identical functions.
f = FinFunction([4,2,3,1], 5)
eq = equalizer([f,f], C)
@test incl(eq) == FinFunction([1,2,3,4], 4)
@test factorize(eq, FinFunction([2,1,3,3], 3)) == FinFunction([2,1,3,3], 4)

# Equalizer matching nothing.
f, g = id(C,FinSet(5)), FinFunction([2,3,4,5,1], 5)
eq = equalizer([f,g],C)
@test incl(eq) == FinFunction(Int[], 5)
@test factorize(eq, FinFunction(Int[], 0)) == FinFunction(Int[], 0)


# Coequalizers
##############

# Coequalizer from a singleton set.
f, g = FinFunction.([[1], [3]], 3)
coeq = coequalizer([f,g], C)
@test proj(coeq) == FinFunction([1,2,1], 2)
@test factorize(coeq, FinFunction([4,1,4], 4)) == FinFunction([4,1], 4)
@test_throws ErrorException factorize(coeq, FinFunction([3,1,4], 4))

# Coequalizer in case of identical functions.
f = FinFunction([4,2,3,1], 5)
coeq = coequalizer([f,f], C)
@test proj(coeq) == FinFunction(1:5, 5)
@test factorize(coeq, FinFunction([2,1,3,3,4],4)) == FinFunction([2,1,3,3,4],4)

# Coequalizer identifying everything.
f, g = id(C,FinSet(5)), FinFunction([2,3,4,5,1], 5)
coeq = coequalizer([f,g], C)
@test proj(coeq) == FinFunction(fill(1,5), 1)
@test factorize(coeq, FinFunction(fill(3,5), 5)) == FinFunction([3], 5)

# Pullbacks 
###########
f, g = FinFunction.([[1,1,3,2],[1,1,4,2]], 4)
lim = pullback(f, g, C);
@test force(proj2(lim)) == FinFunction([1,2,1,2,4], 4)
@test force(proj1(lim)) == FinFunction([1,1,2,2,4], 4)

fg = FinFunction.([[1,2,4],[2,1,4]], 4)
@test force(compose(C,pair(lim,fg), proj1(lim))) == fg[1]
@test force(compose(C,pair(lim,fg), proj2(lim))) == fg[2]

# Pullback from a singleton set: the degenerate case of a product.
lim = pullback(FinFunction.([[1,1],[1,1,1]],1)..., C)
@test ob(lim) == FinSet(6)
@test force(proj1(lim)) == FinFunction([1,2,1,2,1,2], 2)
@test force(proj2(lim)) == FinFunction([1,1,2,2,3,3], 3)

f, g = FinFunction([1,1,2], 2), FinFunction([3,2,1], 3)

@withmodel SetC() (⋅) begin
  @test force(pair(lim,[f,g]) ⋅ proj1(lim)) == f
  @test force(pair(lim,[f,g]) ⋅ proj2(lim)) == g
end

# Pullback of a cospan into non-finite set.
f = FinDomFunction([:a, :a, :c, :b], SetOb(Symbol))
g = FinDomFunction([:a, :a, :d, :b], SetOb(Symbol))
π1, π2 = lim = pullback(f, g, C)
@test ob(lim) == FinSet(5)
@test force(π1) == FinFunction([1,1,2,2,4], 4)
@test force(π2) == FinFunction([1,2,1,2,4], 4)


# Pushouts
#---------

# Pushout from the empty set: the degenerate case of the coproduct.
f, g = FinFunction(Int[], 2), FinFunction(Int[], 3)
colim = pushout(f,g, C)
@test ob(colim) == FinSet(5)
@test force(coproj1(colim)) == FinFunction([1,2], 5)
@test force(coproj2(colim)) == FinFunction([3,4,5], 5)

h, k = FinFunction([3,5], 5), FinFunction([1,2,3], 5)
ℓ = copair(colim, h, k)
@test force(compose(C,coproj1(colim), ℓ)) == h
@test force(compose(C,coproj2(colim), ℓ)) == k

# Pushout from a singleton set.
f, g = FinFunction([1], 2), FinFunction([2], 3)
colim = ι1, ι2 = pushout(f,g, C)
@test ob(colim) == FinSet(4)
@test force(compose(C,f,ι1)) == force(compose(C,g,ι2))
@test force(ι1) == FinFunction([1,2], 4)
@test force(ι2) == FinFunction([3,1,4], 4)

h, k = FinFunction([3,5], 5), FinFunction([1,3,5], 5)
ℓ = copair(colim, h, k)
@test force(compose(C,coproj1(colim), ℓ)) == h
@test force(compose(C,coproj2(colim), ℓ)) == k
k = FinFunction([1,2,5], 5)
@test_throws ErrorException copair(colim,h,k)

h, k = FinDomFunction.([[:b,:c],[:a,:b,:c]], Ref(SetOb(Symbol)))

ℓ = copair(colim, h, k)
@test force(compose(C,coproj1(colim), ℓ)) == h
@test force(compose(C,coproj2(colim), ℓ)) == k
k = FinDomFunction([:a,:d,:c], SetOb(Symbol))
@test_throws ErrorException copair(colim,h,k)

# Same thing as a colimit of a general free diagram.
diagram = FreeDiagram([FinSet(1),FinSet(2),FinSet(3)],[(f,1,2), (g,1,3)])
colim = _, ι1, ι2 = colimit(diagram, C, DefaultAlg())
@test ob(colim) == FinSet(4)
@test force(compose(C,f,ι1)) == force(compose(C,g,ι2))
@test force(ι1) == FinFunction([1,2], 4)
@test force(ι2) == FinFunction([3,1,4], 4)

h, k = FinFunction([3,5], 5), FinFunction([1,3,5], 5)
ℓ = universal(colim, Multicospan([compose(C,f,h), h, k])) # f⋅h == g⋅k
@test force(compose(C,ι1, ℓ)) == h
@test force(compose(C,ι2, ℓ)) == k

# Pushout from a two-element set, with non-injective legs.
f, g = FinFunction([1,1], 2), FinFunction([1,2], 3)
colim = pushout(f,g, C)
@test ob(colim) == FinSet(3)
ι1, ι2 = colim
@test force(compose(C,f,ι1)) == force(compose(C,g,ι2))
@test force(ι1) == FinFunction([1,2], 3)
@test force(ι2) == FinFunction([1,1,3], 3)

# Same thing as a colimit of a general free diagram.
diagram = FreeDiagram([FinSet(2),FinSet(2),FinSet(3)],[(f,1,2),(g,1,3)])
colim = _, ι1, ι2 = colimit(diagram, C, DefaultAlg())
@test ob(colim) == FinSet(3)
@test force(ι1) == FinFunction([1,2], 3)
@test force(ι2) == FinFunction([1,1,3], 3)

# Same thing as a colimit of a bipartite free diagram.
bdiagram = BipartiteFreeDiagram([FinSet(2)], [FinSet(2),FinSet(3)],
                                [(f,1,1),(g,1,2)])
colim = ι1, ι2 = colimit(bdiagram, C, DefaultAlg())
@test ob(colim) == FinSet(3)
@test force(ι1) == FinFunction([1,2], 3)
@test force(ι2) == FinFunction([1,1,3], 3)

colim′ = colimit(BipartiteFreeDiagram{AbsSet,SetFunction}(diagram), C, DefaultAlg())
@test legs(colim′) == legs(colim)

# General limits
#################

# Pullback as limit of free diagram.
f, g = FinFunction([1,1,3,2],4), FinFunction([1,1,4,2],4)
dia = FreeDiagram(BipartiteFreeDiagram(Cospan(f, g)))
lim = limit(dia, C, DefaultAlg())
@test ob(lim) == FinSet(5)
π1, π2 = legs(lim)[1:2]
@test force(π1) == FinFunction([1,2,1,2,4], 4)
@test force(π2) == FinFunction([1,1,2,2,4], 4)

# Pullback using different algorithms.
tuples(lim::Limit) =
  sort!([ Tuple(map(π -> π(i), legs(lim))) for i in ob(lim) ])

f, g = FinFunction.([[3,1,1,5,2],[4,1,1,3,2]],5)

for alg in (NestedLoopJoin(), SortMergeJoin(), HashJoin())
  lim = pullback(f, g, C; alg)
  @test ob(lim) == FinSet(6)
  @test tuples(lim) == [(1,4), (2,2), (2,3), (3,2), (3,3), (5,5)]
end

# Ternary pullback using different algorithms.
f, g = FinDomFunction.([[:a,:b,:c],[:c,:b,:a]], Ref(SetOb(Symbol)))
h = FinDomFunction([:a,:a,:b,:b,:c,:c], SetOb(Symbol))
fgh = Multicospan([f, g, h])
lim = limit(fgh, C, ComposeProductEqualizer())
@test ob(lim) == FinSet(6)
reference_tuples = tuples(lim)

for alg in (NestedLoopJoin(), SortMergeJoin(), HashJoin())
  lim = limit(fgh, C, alg)
  @test ob(lim) == FinSet(6)
  @test tuples(lim) == reference_tuples
end

# Pullback involving a constant, which should be handled specially.
lim = pullback(FinFunction([3], 4), FinFunction([1,3,4,2,3,3], 4), C; alg=SmartJoin())
@test ob(lim)== FinSet(3)
@test getvalue(proj1(lim)) == ConstantFunction(1, FinSet(3), FinSet(1)) 
@test proj2(lim) == FinFunction([2,5,6], 6)


# Pullback as limit of free diagram.
f, g = FinFunction([1,1,3,2],4), FinFunction([1,1,4,2],4)
lim = limit(FreeDiagram(Cospan(f, g)), C, DefaultAlg())
@test ob(lim) == FinSet(5)
π1, π2 = legs(lim)[1:2]
@test force(π1) == FinFunction([1,2,1,2,4], 4)
@test force(π2) == FinFunction([1,1,2,2,4], 4)

f′, g′ = FinFunction([1,2,4], 4), FinFunction([2,1,4], 4)
h = universal(lim, Multispan(FinSet(3),[f′, g′, compose(C, f′,f)])) # f′⋅f == g′⋅g
@test force(compose(C, h, π1)) == f′
@test force(compose(C, h, π2)) == g′

# Pullback as limit of bipartite free diagram.
lim = limit(BipartiteFreeDiagram(Cospan(f, g)), C, DefaultAlg())
π1, π2 = force.(legs(lim))
@test π1 == FinFunction([1,1,2,2,4], 4)
@test π2 == FinFunction([1,2,1,2,4], 4)
lim′ = limit(BipartiteFreeDiagram(Cospan(f, g)), SetC(), DefaultAlg())
@test legs(lim′)[1:2] == legs(lim)

h = universal(lim, Span(f′, g′))
@test force(compose(C, h, π1)) == f′
@test force(compose(C, h, π2)) == g′

# Equalizer as limit of bipartite free diagram.
f, g = [FinDomFunction(x -> x % i, FinSet(100), SetOb(Int)) for i in 2:3]
d = BipartiteFreeDiagram(ParallelMorphisms([f, g]))
lim = (ι,) = limit(d, C, DefaultAlg())
@test ι == incl(equalizer([f, g], C))

# Two pullbacks, which should be reduced to a single pullback by pairing.
f1, f2 = FinDomFunction.([[1,1,2,2,3,3],[1,2,3]], Ref(SetOb(Int))) 
g1, g2 = FinDomFunction.([[:a,:a,:a,:b,:b,:b],[:a,:b,:c]], Ref(SetOb(Symbol)))
d = BipartiteFreeDiagram{AbsSet,FinDomFunction}()
add_vertices₁!(d, 2; ob₁=[FinSet(6), FinSet(3)])
add_vertices₂!(d, 2; ob₂=[SetOb(Int), SetOb(Symbol)])
add_edges!(d, [1,1,2,2], [1,2,1,2], hom=[f1,g1,f2,g2])
lim = π1, π2 = limit(d, C, DefaultAlg())
@test π1 == FinFunction([1,2,4], 6)
@test π2 == FinFunction([1,1,2], 3)


# Colimits with names
#--------------------

# Pushout with names.
A, B = FinSet.(Set.([[:w, :x, :y1],[:x, :y2, :z]]))
f, g = FinFunction(Dict(:y => :y1), A), FinFunction(Dict(:y => :y2), B)
colim = ι1, ι2 = pushout(f, g, C)
X = ob(colim)
@test Set(X) == Set([:w, Symbol("x#1"), Symbol("x#2"), :y, :z])
@test ι1 == FinFunction(Dict(:w => :w, :x => Symbol("x#1"), :y1 => :y), X)
@test ι2 == FinFunction(Dict(:x => Symbol("x#2"), :y2 => :y, :z => :z), X)

end # module
