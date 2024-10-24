module TestSetCLimits 


# Limits
########

# Terminal object.
@test ob(terminal(TypeSet)) == TypeSet(Nothing)
@test delete(terminal(TypeSet), TypeSet(Int))(3) == nothing

# Trivial product.
lim = limit(SingletonDiagram(TypeSet(Int)))
@test ob(lim) == TypeSet(Int)

f = SetFunction(length, TypeSet(Vector{String}), TypeSet(Int))
@test universal(lim, SMultispan{1}(f)) === f

# Binary product.
lim = product(TypeSet(Int), TypeSet(String))
@test ob(lim) == TypeSet(Tuple{Int,String})
π1, π2 = lim
@test (π1((1,"foo")), π2((1,"foo"))) == (1,"foo")

g = SetFunction(v -> sprint(join, v), TypeSet(Vector{String}), TypeSet(String))
@test pair(lim, f, g)(["foo", "bar", "baz"]) == (3, "foobarbaz")

# N-ary product.
lim = product(fill(TypeSet(Int), 3))
@test ob(lim) == TypeSet(Tuple{Int,Int,Int})
π1, π2, π3 = lim
@test (π1((1,2,3)), π2((1,2,3)), π3((1,2,3))) == (1,2,3)

fs = [ SetFunction(x -> x+i, TypeSet(Int), TypeSet(Int)) for i in 1:3 ]
@test pair(lim, fs)(3) == (4,5,6)

# Cartesian monoidal structure.
@test TypeSet(Int) ⊗ TypeSet(String) == TypeSet(Tuple{Int,String})
@test munit(TypeSet) == TypeSet(Nothing)
@test σ(TypeSet(Int), TypeSet(String))((1,"foo")) == ("foo",1)
π1 = proj1(TypeSet(Int), TypeSet(String))
π2 = proj2(TypeSet(Int), TypeSet(String))
@test (π1((1,"foo")), π2((1,"foo"))) == (1,"foo")

@test (f⊗g)((["foo"], ["bar", "baz"])) == (1, "barbaz")
@test Δ(TypeSet(Int))(2) == (2,2)
@test ◊(TypeSet(Int))(1) == nothing

@test otimes(fill(TypeSet(Int), 3)) == TypeSet(Tuple{Int,Int,Int})
@test otimes(fs)((1,5,10)) == (2,7,13)

# Colimits
##########

# Trivial coproduct.
colim = colimit(SingletonDiagram(TypeSet(Int)))
@test ob(colim) == TypeSet(Int)

f = SetFunction(string, TypeSet(Int), TypeSet(String))
@test universal(colim, SMulticospan{1}(f)) === f

# VarSets
S = SetOb(VarSet{Union{}}(5))
@test SetOb(S) == S

end # module