module TestDecidableSets
using Test
using Catlab.CategoricalAlgebra.DecidableSets
using Catlab.Theories

odds = DecidableSet(Int, x -> x % 2 == 1)
evens = DecidableSet(Int, x -> x % 2 == 0)

plus_one_to_odd = DecidableHom(odds,evens,x -> x+1)
plus_one_to_even = DecidableHom(evens,odds,x -> x+1)

@test plus_one_to_odd(1) == 2
@test_throws AssertionError plus_one_to_odd(2) == 3
@test plus_one_to_even(2) == 3
@test_throws AssertionError plus_one_to_even(3) == 4

@test compose(plus_one_to_odd, plus_one_to_even)(3) == 5

plus_two = DecidableHom(odds,evens,x -> x+2)

@test_throws AssertionError plus_two(3)
end
