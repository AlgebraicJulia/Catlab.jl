module TestSets
using Test

using Catlab.Theories, Catlab.CategoricalAlgebra.Sets

# Sets from Julia types
#######################

# Callables.
f = SetFunction(x -> 2x, TypeSet(Int), TypeSet(Int))
g = SetFunction(x -> 3x, TypeSet(Int), TypeSet(Int))
@test dom(f) == TypeSet(Int)
@test codom(f) == TypeSet(Int)
@test f(1) == 2

# Identities.
X = TypeSet(Int)
@test dom(id(X)) == X
@test codom(id(X)) == X
@test id(X)(1) == 1

# Composition.
h = compose(f,g)
@test h(1) == 6
@test compose(id(dom(f)), f) == f
@test compose(f, id(codom(f))) == f

# Predicated sets
#################

odds = PredicatedSet(Int, isodd)
evens = PredicatedSet(Int, iseven)
@test sprint(show, odds) == "PredicatedSet($(Int), isodd)"

plus_one_to_odd = SetFunction(x -> x+1, odds, evens)
plus_one_to_even = SetFunction(x -> x+1, evens, odds)

@test plus_one_to_odd(1) == 2
@test_throws ErrorException plus_one_to_odd(2) == 3
@test plus_one_to_even(2) == 3
@test_throws ErrorException plus_one_to_even(3) == 4

plus_two_to_odd = compose(plus_one_to_odd, plus_one_to_even)
@test plus_two_to_odd(3) == 5
@test dom(plus_two_to_odd) == odds
@test codom(plus_two_to_odd) == odds
@test_throws ErrorException plus_two_to_odd(2) == 4

end
