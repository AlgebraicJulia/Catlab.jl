module TestVarFnLimits 

@test dom(create(VarSet{Int}(1))) == FinSet(0)

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

end # module
