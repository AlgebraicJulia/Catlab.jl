module TestFinSets

using Test, Catlab

sshow(args...) = sprint(show, args...)

# FinSetInt
###########
set = FinSet(3)
@test getvalue(set) isa FinSetInt
@test length(set) == 3
@test collect(set) == 1:3
@test 2 ∈ set && 10 ∉ set
@test sshow(set) == "FinSet(3)"

# Collections as sets.
######################
set = FinSet(Set(1:2:5))
@test getvalue(set) isa FinSetHash
@test length(set) == 3
@test sort!(collect(set)) == [1,3,5]
@test 3 ∈ set && 4 ∉ set
@test startswith(sshow(set), "FinSet(Set(")

# Tables as sets.
#################
set = FinSet((x=[1,3,5], y=["a","b","c"]))
@test getvalue(set) isa TabularSet
@test eltype(set) == NamedTuple{(:x,:y),Tuple{Int,String}}
@test length(set) == 3
@test collect(set) == [(x=1, y="a"), (x=3, y="b"), (x=5, y="c")]
@test startswith(sshow(set), "TabularSet(")
@test startswith(sshow(MIME("text/plain"), set), "3-element TabularSet")
@test startswith(sshow(MIME("text/html"), set), "<div")

# SumFinSet
###########
@test_throws ErrorException FinSet(SumSet([SetOb(Bool), SetOb(Symbol)])) # Not finite
s = FinSet(SumSet([FinSet(2), FinSet([true,false])]))

@test eltype(s) == Union{TaggedElem{Val{1}, Int}, TaggedElem{Val{2}, Bool}}
@test length(s) == 4
@test length(collect(s)) == 4

@test TaggedElem(true, 2) ∈ s
@test TaggedElem(true, 1) ∉ s
@test TaggedElem(1, 1) ∈ s
@test TaggedElem(10, 2) ∉ s
@test TaggedElem(3, 1) ∉ s

@test collect(s) == [TaggedElem(1, 1), TaggedElem(2, 1), TaggedElem(true, 2) , TaggedElem(false, 2)]

# ProdFinSet
############
@test_throws ErrorException FinSet(ProdSet([SetOb(Bool), SetOb(Symbol)])) # Not finite
s =  FinSet(ProdSet([FinSet(2), FinSet([true,false])]))

@test eltype(s) == Tuple{Int,Bool}
@test length(s) == 4

@test (2, true) ∈ s
@test (true, 1) ∉ s 

@test collect(s) == [(1, true), (2, true), (1, false) , (2, false)]


# Empty
###########
s = FinSet()

@test nothing ∉ s
@test 3 ∉ s
@test collect(s) == Union{}[]
@test length(s) == 0

# Singleton
###########
s = FinSet(nothing)

@test nothing ∈ s
@test 3 ∉ s
@test collect(s) == [nothing]
@test length(s) == 1

# Enum
######
@enum MyEnum X Y

s = FinSet(MyEnum) #FinSet(EnumSet{MyEnum}())

@test X ∈ s
@test 3 ∉ s
@test collect(s) == [X, Y]
@test length(s) == 2

end # module
