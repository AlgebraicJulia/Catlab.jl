module TestFinSets

using Test, Catlab

sshow(args...) = sprint(show, args...)

# Finite sets
#############

set = FinSet(3)
@test getvalue(set) isa FinSetInt
@test length(set) == 3
@test collect(set) == 1:3
@test 2 ∈ set && 10 ∉ set
@test sshow(set) == "FinSet(3)"

# Collections as sets.
set = FinSet(Set(1:2:5))
@test getvalue(set) isa FinSetHash
@test length(set) == 3
@test sort!(collect(set)) == [1,3,5]
@test 3 ∈ set && 4 ∉ set
@test startswith(sshow(set), "FinSet(Set(")

# Tables as sets.
set = FinSet((x=[1,3,5], y=["a","b","c"]))
@test getvalue(set) isa TabularSet
@test eltype(set) == NamedTuple{(:x,:y),Tuple{Int,String}}
@test length(set) == 3
@test collect(set) == [(x=1, y="a"), (x=3, y="b"), (x=5, y="c")]
@test startswith(sshow(set), "TabularSet(")
@test startswith(sshow(MIME("text/plain"), set), "3-element TabularSet")
@test startswith(sshow(MIME("text/html"), set), "<div")

end