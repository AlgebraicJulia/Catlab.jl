module TestVarFunctions

using Catlab, Test

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
