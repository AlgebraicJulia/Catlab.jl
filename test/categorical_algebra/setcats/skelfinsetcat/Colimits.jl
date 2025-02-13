module TestSkelFinSetCatColimits

using Catlab, Test

const 𝒞 = SkelFinSet()

# Initial objects
#################
I = initial[𝒞]()
@test I == colimit[𝒞](EmptyDiagram{FinSetInt}())
@test ob[𝒞](I) == FinSetInt(0)
@test collect(create[𝒞](FinSetInt(4))) == Int[]


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