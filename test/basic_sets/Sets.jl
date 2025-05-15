module TestSets

using Test, Catlab

# Sets from Julia types
#######################

# Elementhood for TypeSets
strings = SetOb(String)
@test eltype(strings) == String
@test getvalue(strings) isa TypeSet{String}
@test "hi" ∈ strings
@test 7 ∉ strings

@test 3 ∈ SetOb(Int)
@test :a ∈ SetOb(Symbol)
@test :a ∉ SetOb(Int)

# UnionSets
############

@test :a ∈ SetOb(UnionSet([SetOb(Int), SetOb(Symbol)]))
@test :a ∈ SetOb(UnionSet([SetOb(Symbol), SetOb(Symbol)]))

# Predicated sets
#################

odds = PredicatedSet(Int, isodd) |> SetOb
evens = PredicatedSet(Int, iseven)  |> SetOb
@test sprint(show, getvalue(odds)) == "PredicatedSet(TypeSet($(Int)), isodd)"

@test 1 ∈ odds
@test 2 ∉ odds
@test 2 ∈ evens

# SumSets
#########
s = SetOb(SumSet([SetOb(Bool), SetOb(Symbol)]))
@test eltype(s) == Union{TaggedElem{Val{1}, Bool}, TaggedElem{Val{2}, Symbol}}

@test TaggedElem(true, 1) ∈ s
@test TaggedElem(true, 2) ∉ s 
@test TaggedElem(:x, 2) ∈ s
@test TaggedElem(:x, 3) ∉ s

# ProdSets
##########
s = SetOb(ProdSet([SetOb(Bool), SetOb(Symbol)]))
@test eltype(s) == Tuple{Bool, Symbol}

@test (true, :x) ∈ s
@test (true, true) ∉ s
@test (;) ∉ s
@test (true,) ∉ s

end # module
