module TestSkelFinSetCat 

using Catlab, Test

const 𝒞 = SkelFinSet()

# Initial objects
#################
I = initial[𝒞]()
@test I == colimit[𝒞](EmptyDiagram{FinSetInt}())
@test ob[𝒞](I) == FinSetInt(0)
@test collect(create[𝒞](FinSetInt(4))) == Int[]


# Terminal objects
##################
T = terminal[𝒞]()
@test T == limit[𝒞](EmptyDiagram{FinSetInt}())
@test delete[𝒞](FinSetInt(2)) |> collect == FinFunction([1,1], 1) |> collect

# Products
##########
P = product[𝒞](FinSetInt.([2,2])...)
dia = DiscreteDiagram(FinSetInt.([2,2]))
@test P == limit[𝒞](dia)
fs = FinFunction.([[1,2,1,2],[1,1,2,2]], 2)
@test force.(P) == fs
sp = Span(FinFunction.([[1,2,2],[1,2,1]], 2)...)
@test universal[𝒞](P, sp) == FinFunction([1,4,2]) == pair[𝒞](P, sp...)


P = product[𝒞](FinSetInt(2), FinSetInt(3))
@test ob[𝒞](P) == FinSetInt(6) # really should be a FinSetInt


@test force(proj1(P)) == FinFunction([1,2,1,2,1,2], 2)
@test force(proj2(P)) == FinFunction([1,1,2,2,3,3], 3)

P = product[𝒞](FinSetInt(4), FinSetInt(3))
f, g = FinFunction([2,1,4], 4), FinFunction([1,3,2], 3)
@test force(compose[𝒞](pair[𝒞](P,f,g), proj1(P))) == f
@test force(compose[𝒞](pair[𝒞](P,f,g), proj2(P))) == g

# Coproducts
############
CP = coproduct[𝒞](FinSetInt.([2,2])...)
dd = DiscreteDiagram(FinSetInt.([2,2]))
@test CP == colimit[𝒞](dd)

fs = FinFunction.([[1,2],[3,4]], 4)
sp = Cospan(FinFunction.([[2,3],[1,4]], 4)...)
@test universal[𝒞](CP, sp) == FinFunction([2,3,1,4])


# Cocartesian monoidal
######################
const CM = CocartesianMonoidal(TypedCatWithCoproducts(𝒞))

@withmodel getvalue(CM) (⊕, oplus, mzero, swap, coproj1, coproj2) begin
  @test FinSetInt(2)⊕FinSetInt(3) == FinSetInt(5)
  # @test oplus(FinSet.([2,3,4])) == FinSet(9) # TODO handle lists
  f, g = FinFunction([3,5], 5), FinFunction([1,2,3], 5)
  @test force(f ⊕ g) == FinFunction([3,5,6,7,8], 10)
  @test mzero() == FinSetInt(0)
  f_2_3 = FinSetInt.([2,3])
  @test swap(f_2_3...) == FinFunction([4,5,1,2,3], 5)
  ι1, ι2 = coproj1(f_2_3...), coproj2(f_2_3...)
  @test ι1 == FinFunction([1,2], 5)
  @test ι2 == FinFunction([3,4,5], 5)  
end

# Equalizers
############

f, g = FinFunction.([[1,2,4,3], [3,2,4,1]], 4)
eq = equalizer[𝒞](f, g)
@test incl(eq) == FinFunction([2,3], 4)
@test factorize[𝒞](eq, FinFunction([2,3,2], 3)) == FinFunction([1,2,1], 2)

# Equalizer of identical functions.
f = FinFunction([4,2,3,1], 5)
eq = equalizer[𝒞](f,f)
@test incl(eq) == FinFunction([1,2,3,4], 4)
@test factorize[𝒞](eq, FinFunction([2,1,3,3], 3)) == FinFunction([2,1,3,3], 4)

# Equalizer matching nothing.
f, g = id[𝒞](FinSetInt(5)), FinFunction([2,3,4,5,1], 5)
eq = equalizer[𝒞](f,g)
@test incl(eq) == FinFunction(Int[], 5)
@test factorize[𝒞](eq, FinFunction(Int[], 0)) == FinFunction(Int[], 0)

# Coequalizers
###############

# Coequalizer from a singleton set.
f, g = FinFunction.([[1], [3]], 3)
coeq = coequalizer[𝒞](f,g)
@test proj(coeq) == FinFunction([1,2,1], 2)
@test factorize[𝒞](coeq, FinFunction([4,1,4], 4)) == FinFunction([4,1], 4)

# Coequalizer in case of identical functions.
f = FinFunction([4,2,3,1], 5)
coeq = coequalizer[𝒞](f,f)
@test proj(coeq) == FinFunction(1:5, 5)
@test factorize[𝒞](coeq, FinFunction([2,1,3,3,4],4)) == FinFunction([2,1,3,3,4],4)

# Coequalizer identifying everything.
f, g = id[𝒞](FinSetInt(5)), FinFunction([2,3,4,5,1], 5)
coeq = coequalizer[𝒞](f,g)
@test proj(coeq) == FinFunction(fill(1,5), 1)
@test factorize[𝒞](coeq, FinFunction(fill(3,5), 5)) == FinFunction([3], 5)

# Pullbacks
###########

f, g = FinFunction.([[1,1,3,2],[1,1,4,2]], 4)
lim = pullback[𝒞](f, g);
@test force(proj2(lim)) == FinFunction([1,2,1,2,4], 4)
@test force(proj1(lim)) == FinFunction([1,1,2,2,4], 4)

fg = FinFunction.([[1,2,4],[2,1,4]], 4)

@withmodel 𝒞 (⋅, pullback_pair) begin
  @test force(pullback_pair(lim,fg) ⋅ proj1(lim)) == fg[1]
  @test force(pullback_pair(lim,fg) ⋅ proj2(lim)) == fg[2]
end 

# Pullback from a singleton set: the degenerate case of a product.
lim = pullback[𝒞](FinFunction.([[1,1],[1,1,1]],1)...)
@test ob(lim) == FinSet(6)
@test force(proj1(lim)) == FinFunction([1,2,1,2,1,2], 2)
@test force(proj2(lim)) == FinFunction([1,1,2,2,3,3], 3)

f, g = FinFunction([1,1,2], 2), FinFunction([3,2,1], 3)

@withmodel 𝒞 (⋅, pullback_pair) begin
  @test force(pullback_pair(lim,[f,g]) ⋅ proj1(lim)) == f
  @test force(pullback_pair(lim,[f,g]) ⋅ proj2(lim)) == g
end

# Pushouts
##########

# Pushout from the empty set: the degenerate case of the coproduct.
f, g = FinFunction(Int[], 2), FinFunction(Int[], 3)
colim = pushout[𝒞](f,g)
@test ob(colim) == FinSetInt(5)
@test force(coproj1(colim)) == FinFunction([1,2], 5)
@test force(coproj2(colim)) == FinFunction([3,4,5], 5)

h, k = FinFunction([3,5], 5), FinFunction([1,2,3], 5)
ℓ = copair[𝒞](colim, h, k)

@withmodel 𝒞 (⋅) begin
  @test force(coproj1(colim) ⋅ ℓ) == h
  @test force(coproj2(colim) ⋅ ℓ) == k
end

# Pushout from a singleton set.
f, g = FinFunction([1], 2), FinFunction([2], 3)
colim = ι1, ι2 = pushout[𝒞](f,g)
@test ob(colim) == FinSetInt(4)

@withmodel 𝒞 (⋅) begin
  @test force(f⋅ι1) == force(g⋅ι2)
  @test force(ι1) == FinFunction([1,2], 4)
  @test force(ι2) == FinFunction([3,1,4], 4)
end 

h, k = FinFunction([3,5], 5), FinFunction([1,3,5], 5)

ℓ = pushout_copair[𝒞](colim, h, k)

@withmodel 𝒞 (⋅) begin
  @test force(coproj1(colim) ⋅ ℓ) == h
  @test force(coproj2(colim) ⋅ ℓ) == k
end

# General FreeGraph Limits
##########################

# Pullback as limit of free diagram.
f, g = FinFunction([1,1,3,2],4), FinFunction([1,1,4,2],4)
dia = BipartiteFreeDiagram(Cospan(f, g; cat=𝒞))
lim = limit[𝒞](dia)
@test ob(lim) == FinSet(5)
π2, π1 = legs(lim)[1:2] # TODO order is different?
@test force(π1) == FinFunction([1,2,1,2,4], 4)
@test force(π2) == FinFunction([1,1,2,2,4], 4)

# Pullback using different algorithms.
tuples(lim::AbsLimit) =
  sort!([ Tuple(map(π -> π(i), legs(lim))) for i in ob(lim) ])

# TODO: uniform interface for the different algorithms? #
# f, g = FinFunction.([[3,1,1,5,2],[4,1,1,3,2]],5)
# for alg in (NestedLoopJoin(), SortMergeJoin(), HashJoin())
#   lim = pullback(f, g; alg)
#   @test ob(lim) == FinSet(6)
#   @test tuples(lim) == [(1,4), (2,2), (2,3), (3,2), (3,3), (5,5)]
# end


# Pullback involving a constant, which should be handled specially.
lim = pullback[𝒞](FinFunction([3], 4), FinFunction([1,3,4,2,3,3], 4))
@test ob(lim)== FinSetInt(3)
@test getvalue(proj1(lim)) == ConstantFunction(1, FinSet(3), FinSet(1)) 
@test proj2(lim) == FinFunction([2,5,6], 6)

# Pullback as limit of free diagram.
f, g = FinFunction([1,1,3,2],4), FinFunction([1,1,4,2],4)
d = FreeGraph(FreeDiagram(Cospan(f, g)))
lim = limit[𝒞](d)
@test ob(lim) == FinSetInt(5)
_, π1, π2 = force.(legs(lim)) # TODO order different?
@test force(π1) == FinFunction([1,2,1,2,4], 4)
@test force(π2) == FinFunction([1,1,2,2,4], 4)

f′, g′ = FinFunction([1,2,4], 4), FinFunction([2,1,4], 4)

h = universal[𝒞](lim, Multispan(FinSetInt(3),[compose[𝒞](f′,f), f′, g′]; cat=𝒞)) # f′⋅f == g′⋅g
@test force(compose[𝒞]( h, π1)) == f′
@test force(compose[𝒞]( h, π2)) == g′

# Pullback as limit of bipartite free diagram.
bpd = BipartiteFreeDiagram(Cospan(f, g; cat=𝒞))
lim = limit[𝒞](bpd)
π1, π2 = force.(legs(lim))
@test π1 == FinFunction([1,1,2,2,4], 4)
@test π2 == FinFunction([1,2,1,2,4], 4)

h = universal[𝒞](lim, Span(f′, g′; cat=𝒞))
@test force(compose[𝒞](h, π1)) == f′
@test force(compose[𝒞](h, π2)) == g′

# General FreeGraphs Colimits
#############################

# Same thing as a colimit of a general free diagram.
f, g = FinFunction([1], 2), FinFunction([2], 3)

diagram = FreeGraph(FinSetInt.(1:3),[(f,1,2), (g,1,3)]; cat=𝒞)
colim = _, ι1, ι2 = colimit[𝒞](diagram)
@test ob(colim) == FinSetInt(4)
@test force(compose[𝒞](f,ι1)) == force(compose[𝒞](g,ι2))
@test force(ι1) == FinFunction([1,2], 4)
@test force(ι2) == FinFunction([3,1,4], 4)

h, k = FinFunction([3,5], 5), FinFunction([1,3,5], 5)
ℓ = universal[𝒞](colim, Multicospan([compose[𝒞](f,h), h, k]; cat=𝒞)) # f⋅h == g⋅k
@test force(compose[𝒞](ι1, ℓ)) == h
@test force(compose[𝒞](ι2, ℓ)) == k

# Pushout from a two-element set, with non-injective legs.
f, g = FinFunction([1,1], 2), FinFunction([1,2], 3)
colim = ι1, ι2 = pushout[𝒞](f,g)
@test ob(colim) == FinSetInt(3)
@test force(compose[𝒞](f,ι1)) == force(compose[𝒞](g,ι2))
@test force(ι1) == FinFunction([1,2], 3)
@test force(ι2) == FinFunction([1,1,3], 3)

# Same thing as a colimit of a general free diagram.
diagram = FreeGraph(FinSetInt.([2,2,3]),[(f,1,2),(g,1,3)]; cat=𝒞)
colim = _, ι1, ι2 = colimit[𝒞](diagram)
@test ob(colim) == FinSetInt(3)
@test force(ι1) == FinFunction([1,2], 3)
@test force(ι2) == FinFunction([1,1,3], 3)

# Same thing as a colimit of a bipartite free diagram.
bdiagram = BipartiteFreeDiagram([FinSetInt(2)], [FinSetInt(2),FinSetInt(3)],
                                [(f,1,1),(g,1,2)]; cat=𝒞)
colim = ι1, ι2 = colimit[𝒞](bdiagram)
@test ob(colim) == FinSetInt(3)
@test force(ι1) == FinFunction([1,2], 3)
@test force(ι2) == FinFunction([1,1,3], 3)

end # module
