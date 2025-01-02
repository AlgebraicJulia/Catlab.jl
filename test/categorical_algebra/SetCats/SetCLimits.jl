module TestSetCLimits 

using Test, Catlab

# Limits
########

const C = Category(TypeCat(SetC()))
const TC = CatWithTerminal(SetC())
const PC = CatWithProducts(SetC())
const CMC = CartesianMonoidal(TypedCatWithProducts(SetC()))

# Terminal object.
#------------------
T = terminal(TC)
@test ob(T) == FinSet(nothing)
@test delete(TC, T, SetOb(Int))(3) === nothing
@test ◊(TC, SetOb(Int))(3) === nothing

# Trivial product.
#-----------------
lim = limit(C, SingletonDiagram(SetOb(Int)))
@test ob(lim) == SetOb(Int)

f = SetFunction(length, SetOb(Vector{String}), SetOb(Int))
@test universal(C, lim, Multispan([f])) === f

# Binary product.
#-----------------
DD = DiscreteDiagram([SetOb(Int), SetOb(String)])
lim = product(PC, DD)
@test ob(lim) == SetOb(ProdSet([SetOb(Int), SetOb(String)]))
π1, π2 = lim
@test (π1((1,"foo")), π2((1,"foo"))) == (1,"foo")

f = SetFunction(length, SetOb(Vector{String}), SetOb(Int))
g = SetFunction(v -> sprint(join, v), SetOb(Vector{String}), SetOb(String))
@test pair(PC, lim, f, g)(["foo", "bar", "baz"]) == (3, "foobarbaz")



# N-ary product.
#----------------
lim = product(PC, fill(SetOb(Int), 3)...)
@test eltype(ob(lim)) == (Tuple{Int,Int,Int})
π1, π2, π3 = lim
@test (π1((1,2,3)), π2((1,2,3)), π3((1,2,3))) == (1,2,3)

fs = [ SetFunction(x -> x+i, SetOb(Int), SetOb(Int)) for i in 1:3 ]
@test pair(PC, lim, fs)(3) == (4,5,6)

# Cartesian monoidal structure.
#------------------------------
@withmodel getvalue(CMC) (⊗, munit, σ, proj1, proj2, Δ, ◊, id) begin
  @test eltype(SetOb(Int) ⊗ SetOb(String)) == Tuple{Int,String}
  @test munit() == FinSet(nothing)
  @test σ(SetOb(Int), SetOb(String))((1,"foo")) == ("foo",1)
  π1 = proj1(SetOb(Int), SetOb(String))
  π2 = proj2(SetOb(Int), SetOb(String))
  @test (π1((1,"foo")), π2((1,"foo"))) == (1,"foo")
  @test (f⊗g)((["foo"], ["bar", "baz"])) == (1, "barbaz")
  @test Δ(SetOb(Int))(2) == (2,2)
  @test ◊(SetOb(Int))(1) == nothing
end

# TODO
# @test eltype(otimes(CMC, fill(SetOb(Int), 3)...)) == Tuple{Int,Int,Int}
# @test otimes(CMC, fs)((1,5,10)) == (2,7,13)


# Pullback of a cospan into non-finite set.
f = FinDomFunction([:a, :a, :c, :b], SetOb(Symbol))
g = FinDomFunction([:a, :a, :d, :b], SetOb(Symbol))
π1, π2 = lim = pullback[𝒞](f, g)
@test ob(lim) == FinSet(5)
@test force(π1) == FinFunction([1,1,2,2,4], 4)
@test force(π2) == FinFunction([1,2,1,2,4], 4)


# Colimits
##########

# Trivial coproduct.
colim = colimit(SingletonDiagram(SetOb(Int)))
@test ob(colim) == TypeSet(Int)

f = SetFunction(string, TypeSet(Int), TypeSet(String))
@test universal(colim, SMulticospan{1}(f)) === f

# VarSets
S = SetOb(VarSet{Union{}}(5))
@test SetOb(S) == S

# pushouts
# TODO check that input cospan commutes?
# k = FinFunction([1,2,5], 5)
# @test_throws ErrorException copair(colim,h,k)

h, k = FinDomFunction.([[:b,:c],[:a,:b,:c]], Ref(SetOb(Symbol)))

ℓ = copair(colim, h, k)
@test force(compose(C,coproj1(colim), ℓ)) == h
@test force(compose(C,coproj2(colim), ℓ)) == k
k = FinDomFunction([:a,:d,:c], SetOb(Symbol))
@test_throws ErrorException copair(colim,h,k)


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

end # module