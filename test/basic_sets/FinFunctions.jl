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
@test map(FinFunction(FinSet(3)), 1:3) == [1,2,3]

# Composition.
force_compose(x...) = force(FinFunction(x...))
@test force_compose(f,g) == FinFunction([1,2,2], 3)
@test force_compose(g,h) == FinFunction([3,3,1,1,2], 3)
@test force_compose(k,ℓ) == FinFunction(Dict(:a => 1, :b => 1, :c => 4), FinSet(4))
@test force_compose(force_compose(f,g),h) == force_compose(f,force_compose(g,h))
@test force_compose(FinFunction(dom(f)), f) == f
@test force_compose(f, FinFunction(codom(f))) == f


# Indexing.
f = FinFunction([1,3,4], 5)
@test !is_indexed(f)
@test is_indexed(FinFunction(FinSet(3)))
@test preimage(FinFunction(FinSet(3)), 2) == [2]

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
@test force_compose(f,g) == FinFunction([5,4,5,3], 5; index=true)

# Pretty-print.
@test sshow(FinFunction(rot3, FinSet(3), FinSet(3))) ==
  "FinFunction(rot3, FinSet(3), FinSet(3))"
@test sshow(FinFunction(FinSet(3))) == "id(FinSet(3))"
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
@test force(FinDomFunction(f, k)) == FinDomFunction([:a,:c,:d], SetOb(Symbol))

# Indexing.
@test !is_indexed(k)
@test preimage(k, :c) == [3]

k = FinFunction(5:10, 10)
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
@test force(FinDomFunction(f,k)) == FinDomFunction([:a,:a,:b], SetOb(Symbol); index=true)

# Codomain checks
#################

three = FinSet(3)
four = FinSet(4)
badfunc = [1,5,2]
strfunc = ["one","two","three"]
strings = SetOb(String)

f = FinFunction(badfunc,three,four,check=false)
g = FinDomFunction(strfunc,strings,check=true) #known_correct does nothing
h = FinDomFunction(strfunc,strings,index=true,check=true) #known_correct does nothing

@test_throws ErrorException h = FinFunction(badfunc,four,index=true, check=true)
@test_throws ErrorException l = FinFunction(badfunc,four; check=true)
@test_throws ErrorException m = FinFunction(badfunc,four,index=true, check=true)

# Casting Fin(Dom)Functions
############################
f = FinFunction([1,3,4], 5)
f′ = FinDomFunction(f)
f′′ = SetFunction(f′)
f′′′ = SetFunction(f)
@test f′′ == f′′′

end # module
