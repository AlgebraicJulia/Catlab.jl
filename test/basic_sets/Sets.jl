module TestSets 

using Catlab, Test

# Sets from Julia types
#######################

# Elementhood for TypeSets
strings = TypeSet(String)
@test eltype(strings) == String

@test "hi" ∈ strings
@test 7 ∉ strings

@test 3 ∈ TypeSet(Int)
@test :a ∈ TypeSet(Symbol)
@test :a ∉ TypeSet(Int)

# PredicatedSets
################
odds = PredicatedSet(Int, isodd)
evens = PredicatedSet(Int, iseven)
@test sprint(show, odds) == "PredicatedSet($(Int), isodd)"

# SumSets
#########

# ProdSets
##########

end # module