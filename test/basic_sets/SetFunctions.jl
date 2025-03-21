module TestSetFunctions

using Test, Catlab

# Identities.
#-------------
X = SetOb(Int)

i = SetFunction(IdentityFunction(X))
@test i(1) == 1
startswith(sprint(show, i), "id(")

# Callables
#-----------

f = SetFunction(x -> 2x, SetOb(Int), SetOb(Int))
g = SetFunction(x -> 3x, SetOb(Int), SetOb(Int))
@test getvalue(f) isa CallableFunction
@test dom(f) == SetOb(Int)
@test codom(f) == SetOb(Int)
@test f(1) == 2

@test SetFunction(f,g)(1) == 6


# Constants.
#------------

c = SetFunction(ConstantFunction("foo", SetOb(Int)))
@test getvalue(c) isa ConstantFunction
@test dom(c) == SetOb(Int)
@test codom(c) == SetOb(String)
@test c(1) == "foo"

c = SetFunction(ConstantFunction(5, SetOb(Int)))
@test force(SetFunction(c, f)) == SetFunction(ConstantFunction(f(5), SetOb(Int)))
@test force(SetFunction(f, c)) == c
@test force(SetFunction(c, c)) == c


# Predicated sets
#----------------

odds = PredicatedSet(Int, isodd) |> SetOb
evens = PredicatedSet(Int, iseven)  |> SetOb

plus_one_to_odd = SetFunction(x -> x+1, odds, evens)
plus_one_to_even = SetFunction(x -> x+1, evens, odds)

@test plus_one_to_odd(1) == 2
@test_throws ErrorException plus_one_to_odd(2) == 3
@test plus_one_to_even(2) == 3
@test_throws ErrorException plus_one_to_even(3) == 4

plus_two_to_odd = SetFunction(plus_one_to_odd, plus_one_to_even)
@test plus_two_to_odd(3) == 5
@test dom(plus_two_to_odd) == odds
@test codom(plus_two_to_odd) == odds
@test_throws ErrorException plus_two_to_odd(2) == 4

end # module
