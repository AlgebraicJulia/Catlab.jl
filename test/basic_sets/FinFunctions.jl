module TestFinFunctions 

using Test, Catlab

sshow(args...) = sprint(show, args...)

# Functions between finite sets
###############################

f = FinFunction([1,3,4], 5)
g = FinFunction([1,1,2,2,3], 3)
h = FinFunction([3,1,2], 3)
k = FinFunction([1,3,4],3,5)
@test f isa FinFunction
@test getvalue(f) isa FinFunctionVector
@test (dom(f), codom(f)) == (FinSet(3), FinSet(5))
@test force(f) === f
@test codom(FinFunction([1,3,4], 4)) == FinSet(4)
@test k == f 


X = FinSet(Set([:w,:x,:y,:z]))
k = FinFunction(Dict(:a => :x, :b => :y, :c => :z), X)
ℓ = FinFunction(Dict(:w => 2, :x => 1, :y => 1, :z => 4), FinSet(4))
@test getvalue(ℓ) isa FinFunctionDict
@test getvalue(dom(ℓ)) isa FinSetHash{Symbol}
@test (dom(k), codom(k)) == (FinSet(Set([:a, :b, :c])), X)
@test (dom(ℓ), codom(ℓ)) == (X, FinSet(4))
@test force(k) === k
@test codom(FinFunction(Dict(:a => :x, :b => :y, :c => :z))) ==
  FinSet(Set([:x,:y,:z]))

# Evaluation.
rot3(x) = (x % 3) + 1
@test map(f, 1:3) == [1,3,4]
@test map(k, [:a,:b,:c]) == [:x,:y,:z]
@test map(FinFunction(rot3, FinSet(3), FinSet(3)), 1:3) == [2,3,1]
@test map(id[SetC()](FinSet(3)), 1:3) == [1,2,3]

# Composition.
force_compose(x...) = force(compose[SetC()](x...))
@test force_compose(f,g) == FinFunction([1,2,2], 3)
@test force_compose(g,h) == FinFunction([3,3,1,1,2], 3)
@test force_compose(k,ℓ) == FinFunction(Dict(:a => 1, :b => 1, :c => 4), FinSet(4))
@test force_compose(compose[SetC()](f,g),h) == force_compose(f,compose[SetC()](g,h))
@test force_compose(id[SetC()](dom(f)), f) == f
@test force_compose(f, id[SetC()](codom(f))) == f


# Indexing.
@test !is_indexed(f)
@test is_indexed(id[SetC()](FinSet(3)))
@test preimage(id[SetC()](FinSet(3)), 2) == [2]

f = FinFunction([1,2,1,3], 5, index=true)
l = FinFunction([1,2,1,3],4,5,index=true)
@test is_indexed(f)
@test f == l
@test force(f) === f
@test (dom(f), codom(f)) == (FinSet(4), FinSet(5))
@test f(1) == 1
@test preimage(f, 1) == [1,3]
@test preimage(f, 3) == [4]
@test isempty(preimage(f, 4))

g = FinFunction(5:-1:1, 5)
@test force_compose(f,g) == FinFunction([5,4,5,3], 5)

# Pretty-print.
@test sshow(FinFunction(rot3, FinSet(3), FinSet(3))) ==
  "SetFunction(rot3, FinSet(3), FinSet(3))"
@test sshow(id[SetC()](FinSet(3))) == "id(FinSet(3))"
@test sshow(FinFunction([1,3,4], 5)) == "FinFunction($([1,3,4]), FinSet(5))"
@test sshow(FinFunction([1,3,4], 5, index=true)) ==
  "FinFunction($([1,3,4]), FinSet(5), index=true)"
@test sshow(FinFunction(Dict(:a => 1, :b => 3), FinSet(3))) ==
  "FinFunction($(Dict(:a => 1, :b => 3)), FinSet(3))"

# Injectivity / Surjectivity.
f = FinFunction([1,3,4], 4)
g = FinFunction([1,1,2], 2)
X = FinSet(Set([:x,:y,:z]))
k = FinFunction(Dict(:a => :x, :b => :y, :c => :z), X)

@test is_monic(f)
@test !is_epic(f)
@test !is_iso(f)
@test is_epic(g)
@test !is_monic(g)
@test is_monic(k)
@test is_epic(k)
@test is_iso(k)

# Functions out of finite sets
##############################

k = FinDomFunction([:a,:b,:c,:d,:e], SetOb(Symbol))
@test (dom(k), codom(k)) == (FinSet(5), SetOb(Symbol))
@test k(3) == :c
@test collect(k) == [:a,:b,:c,:d,:e]
@test sshow(k) ==
  "FinDomFunction($([:a,:b,:c,:d,:e]), TypeSet(Symbol))"

f = FinFunction([1,3,4], 5)
@test force_compose(f,k) == FinDomFunction([:a,:c,:d], SetOb(Symbol))

# Indexing.
@test !is_indexed(k)
@test preimage(k, :c) == [3]

k = FinDomFunction(5:10, 10)
@test !is_indexed(k) # why would this have been indexed before?
@test preimage(k, 6) == [2]
@test isempty(preimage(k, 4))

k = FinDomFunction([:a,:b,:a,:c], SetOb(Symbol), index=true)
@test is_indexed(k)
@test (dom(k), codom(k)) == (FinSet(4), SetOb(Symbol))
@test k(1) == :a
@test preimage(k, :a) == [1,3]
@test preimage(k, :c) == [4]
@test isempty(preimage(k, :d))
@test sshow(k) ==
  "FinDomFunction($([:a,:b,:a,:c]), TypeSet(Symbol), index=true)"

f = FinFunction([1,3,2], 4)
@test force_compose(f,k) == FinDomFunction([:a,:a,:b], SetOb(Symbol))

# Codomain checks
#################

if false # Reimplement this later
  three = FinSet(3)
  four = FinSet(4)
  badfunc = [1,5,2]
  strfunc = ["one","two","three"]
  strings = TypeSet(String)

  f = FinFunction(badfunc,three,four,check=true)
  g = FinDomFunction(strfunc,strings,known_correct=false) #known_correct does nothing
  h = FinDomFunction(strfunc,strings,index=true,known_correct=true) #known_correct does nothing

  @test_throws ErrorException h = FinFunction(badfunc,four,index=true)
  @test_throws ErrorException l = FinFunction(badfunc,four)
  @test_throws ErrorException m = FinFunction(badfunc,four,index=true)
  @test_throws BoundsError n = FinFunction(badfunc,four,index=true,known_correct=true) 
end 

# VarFunctions
##############
# Construction
const AV = AttrVal
const CV = AttrC{Vector{Int}}()
f = VarFunction{Vector{Int}}([1,AV([1,2,3])], FinSet(1))
@test dom[CV](f) == FinSet(2)
@test codom[CV](f) == FinSet(1)

@test f(AV([1,2])) == AV([1,2])
@test f(1) == 1
@test f(2) == AV([1,2,3])

# Composition 

f = VarFunction{Bool}(([2, 1, AV(true)]),FinSet(3))
g = FinFunction([2,3], 3)
h = FinFunction([2,2,1], 3)
force_compose(x,y) = force(compose[AttrC{Bool}()](x,y))

ff = force_compose(f, f)
ff(3)
collect(ff)
@test force_compose(f, f) |> collect == [1,2, AV(true)]

@test collect(force_compose(g, f)) == [1,AV(true)]
@test collect(force_compose(f,h)) == [2, 2, AV(true)]

@test force(f) == f
@test f.(3:-1:1) == [AV(true), 1, 2]
@test length(f) == 3
@test preimage(f, AV(false)) == []
@test preimage(f, AV(true)) == [3]
@test preimage(f, 2) == [1]

# TODO loose var functions ... maybe? 
# f1 = LooseVarFunction{Bool,Int}(
#   [AttrVar(2),AttrVar(1), 3],
#   SetFunction(x->x ? 10 : 20,TypeSet(Bool),TypeSet(Int)), 
#   FinSet(3))
# f2 = LooseVarFunction{Int,String}(
#   ["a",AttrVar(1), AttrVar(2)],
#   SetFunction(string,TypeSet(Int),TypeSet(String)), 
#   FinSet(2))
# f12 = f1 ⋅ f2 
# @test f12.([false,true]) == ["20","10"]
# @test collect(f1 ⋅ f2) == [AttrVar(1),"a", "3"]


# Monos and epis
f = VarFunction{Bool}([2,1], FinSet(2))
@test is_monic(f) && is_epic(f)
f = VarFunction{Bool}([2,1],FinSet(3))
@test is_monic(f) && !is_epic(f)
f = VarFunction{Bool}([1,1],FinSet(1))
@test !is_monic(f) && is_epic(f)
f = VarFunction{Bool}([1,1,AV(true)],FinSet(2))
@test !(is_monic(f) || is_epic(f))
f = VarFunction{Bool}([1,2,AV(true)],FinSet(2))
@test !is_monic(f) && is_epic(f)


end # module
