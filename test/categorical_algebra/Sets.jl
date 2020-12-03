module TestSets
using Test

using Catlab.Theories, Catlab.CategoricalAlgebra.Sets

# Sets from Julia types
#######################

IntSet = TypeSet{Int}()
f = SetFunction(x -> 2x, IntSet, IntSet)
g = SetFunction(x -> 3x, IntSet, IntSet)

# Callables.
@test dom(f) == IntSet
@test codom(f) == IntSet
@test f(1) == 2

# Identities.
@test dom(id(IntSet)) == IntSet
@test codom(id(IntSet)) == IntSet
@test id(IntSet)(1) == 1

# Composition.
h = compose(f,g)
@test h(1) == 6
@test compose(id(dom(f)), f) == f
@test compose(f, id(codom(f))) == f

# Predicated sets
#################

odds = PredicatedSet{Int}(x -> x % 2 == 1)
evens = PredicatedSet{Int}(x -> x % 2 == 0)

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
