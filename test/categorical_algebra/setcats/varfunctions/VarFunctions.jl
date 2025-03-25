using Catlab, Test

# VarFunctions
##############
# VarSets
S = SetOb(VarSet{Union{}}(5))
@test SetOb(S) == S

# Construction 
f = VarFunction{Vector{Int}}([AttrVar(1),[1,2,3]], FinSet(1))
g = VarFunction{Vector{Int}}(FinDomFunction([AttrVar(1),[1,2,3]]),FinSet(1))
@test f == g
@test f([1,2]) == [1,2]
@test f(AttrVar(2)) == [1,2,3]

# Composition 
f = VarFunction{Bool}(([AttrVar(2),AttrVar(1), true]),FinSet(3))
g = FinFunction([2,3])
h = FinFunction([2,2,1])
@test collect(f⋅ f) == [AttrVar(1),AttrVar(2), true]
@test collect(compose(g,f)) == [AttrVar(1),true]
@test collect(compose(f,h)) == [AttrVar(2),AttrVar(2), true]

@test force(f) == f
@test f.(AttrVar.(3:-1:1)) == [true, AttrVar.(1:2)...]
@test length(f) == 3
@test preimage(f, false) == []
@test preimage(f, true) == [3]
@test preimage(f, AttrVar(2)) == [1]

f1 = LooseVarFunction{Bool,Int}(
  [AttrVar(2),AttrVar(1), 3],
  SetFunction(x->x ? 10 : 20,TypeSet(Bool),TypeSet(Int)), 
  FinSet(3))
f2 = LooseVarFunction{Int,String}(
  ["a",AttrVar(1), AttrVar(2)],
  SetFunction(string,TypeSet(Int),TypeSet(String)), 
  FinSet(2))
f12 = f1 ⋅ f2 
@test f12.([false,true]) == ["20","10"]
@test collect(f1 ⋅ f2) == [AttrVar(1),"a", "3"]

# Monos and epis
f = VarFunction{Bool}(AttrVar.([2,1]),FinSet(2))
@test is_monic(f) && is_epic(f)
f = VarFunction{Bool}(AttrVar.([2,1]),FinSet(3))
@test is_monic(f) && !is_epic(f)
f = VarFunction{Bool}(AttrVar.([1,1]),FinSet(1))
@test !is_monic(f) && is_epic(f)
f = VarFunction{Bool}(AttrVar.([1,1,true]),FinSet(2))
@test !(is_monic(f) || is_epic(f))
f = VarFunction{Bool}(AttrVar.([1,2,true]),FinSet(2))
@test !is_monic(f) && is_epic(f)

# Create 
@test dom(create(VarSet{Int}(1))) == VarSet{Int}(0)

# VarSets to FinSets
#############
f = FinDomFunction([:a, :b, :c])
@test FinDomFunction(f) == f

s = VarSet{Union{}}(2)
@test SetOb(s) == FinSet(s)

@test SetOb(VarSet{Int}(4)) == TypeSet(Union{AttrVar,Int64})

f = VarFunction{Bool}(AttrVar.([1, 2]), FinSet(2))
fin_f = FinDomFunction(Union{AttrVar,Bool}[AttrVar(1), AttrVar(2)], FinSet(2), TypeSet(Union{AttrVar,Bool}))
@test FinDomFunction(f) == fin_f

f = FinDomFunction([:a, :b, :a], FinSet(3), TypeSet(Symbol))
@test f(1) == :a
@test f(2) == :b
@test f(3) == :a
