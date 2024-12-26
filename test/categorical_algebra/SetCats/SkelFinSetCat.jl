module TestSkelFinSetCat 

using Catlab, Test

const C = SkelFinSet()
const TC = CatWithTerminal(C)
const IC = CatWithInitial(C)
const PC = CatWithProducts(C)
const EC = CatWithEqualizers(C) 
const CPC = CatWithCoproducts(C)
const CEC = CatWithCoequalizers(C) 

# Initial objects
#################
I = initial(IC)
@test I == colimit(IC, EmptyDiagram{FinSetInt}())
@test ob(IC, I) == FinSetInt(0)
@test collect(create(IC, FinSetInt(4)) ) == Int[]


# Terminal objects
##################
T = terminal(TC)
@test T == limit(TC, EmptyDiagram{FinSetInt}())
@test delete(TC, FinSetInt(2)) |> collect == FinFunction([1,1], 1) |> collect

# Products
##########
P = product(PC, FinSetInt.([2,2])...)
dia = DiscreteDiagram(FinSetInt.([2,2]))
@test P == limit(PC, dia)
fs = FinFunction.([[1,2,1,2],[1,1,2,2]], 2)
@test force.(P) == fs
sp = Span(FinFunction.([[1,2,2],[1,2,1]], 2)...)
@test universal(PC, P, sp) == FinFunction([1,4,2]) == pair(PC, P, sp...)


P = product(PC, FinSetInt(2), FinSetInt(3))
@test ob(P) == FinSetInt(6) # really should be a FinSetInt


@test force(proj1(P)) == FinFunction([1,2,1,2,1,2], 2)
@test force(proj2(P)) == FinFunction([1,1,2,2,3,3], 3)

P = product(PC, FinSetInt(4), FinSetInt(3))
f, g = FinFunction([2,1,4], 4), FinFunction([1,3,2], 3)
@test force(compose(PC, pair(PC,P,f,g), proj1(P))) == f
@test force(compose(PC, pair(PC,P,f,g), proj2(P))) == g

# Coproducts
############
CP = coproduct(CPC, FinSetInt.([2,2])...)
dd = DiscreteDiagram(FinSetInt.([2,2]))
@test CP == colimit(CPC, dd)

fs = FinFunction.([[1,2],[3,4]], 4)
sp = Cospan(FinFunction.([[2,3],[1,4]], 4)...)
@test universal(CPC, CP, sp) == FinFunction([2,3,1,4])


# Cocartesian monoidal
######################
const CM = CocartesianMonoidal(TypedCatWithCoproducts(CPC))

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
eq = equalizer(EC, f, g)
@test incl(eq) == FinFunction([2,3], 4)
@test factorize(EC, eq, FinFunction([2,3,2], 3)) == FinFunction([1,2,1], 2)

# Equalizer of identical functions.
f = FinFunction([4,2,3,1], 5)
eq = equalizer(EC, f,f)
@test incl(eq) == FinFunction([1,2,3,4], 4)
@test factorize(EC, eq, FinFunction([2,1,3,3], 3)) == FinFunction([2,1,3,3], 4)

# Equalizer matching nothing.
f, g = id[C](FinSetInt(5)), FinFunction([2,3,4,5,1], 5)
eq = equalizer(EC, f,g)
@test incl(eq) == FinFunction(Int[], 5)
@test factorize(EC, eq, FinFunction(Int[], 0)) == FinFunction(Int[], 0)

# Coequalizers
###############

# Coequalizer from a singleton set.
f, g = FinFunction.([[1], [3]], 3)
coeq = coequalizer(CEC, f,g)
@test proj(coeq) == FinFunction([1,2,1], 2)
@test factorize(CEC, coeq, FinFunction([4,1,4], 4)) == FinFunction([4,1], 4)

# Coequalizer in case of identical functions.
f = FinFunction([4,2,3,1], 5)
coeq = coequalizer(CEC, f,f)
@test proj(coeq) == FinFunction(1:5, 5)
@test factorize(CEC, coeq, FinFunction([2,1,3,3,4],4)) == FinFunction([2,1,3,3,4],4)

# Coequalizer identifying everything.
f, g = id[C](FinSetInt(5)), FinFunction([2,3,4,5,1], 5)
coeq = coequalizer(CEC, f,g)
@test proj(coeq) == FinFunction(fill(1,5), 1)
@test factorize(CEC, coeq, FinFunction(fill(3,5), 5)) == FinFunction([3], 5)

end # module
