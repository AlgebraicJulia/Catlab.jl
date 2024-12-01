module TestSetFunctions

using Test, Catlab

# Identities.
#-------------

X = SetOb(Int)
@withmodel SetC() (id) begin 
  @test dom(id(X)) == X
  @test codom(id(X)) == X
  @test id(X)(1) == 1
  @test startswith(sprint(show, id(X)), "id(")
end

# Callables
#-----------

f = SetFunction(x -> 2x, SetOb(Int), SetOb(Int))
g = SetFunction(x -> 3x, SetOb(Int), SetOb(Int))
@test getvalue(f) isa SetFunctionCallable
@test dom(f) == SetOb(Int)
@test codom(f) == SetOb(Int)
@test f(1) == 2

# Composition.
#-------------

@withmodel SetC() (id, compose) begin 
  h = compose(f,g)
  @test dom(h) == dom(f)
  @test codom(h) == codom(g)
  @test h(1) == 6
  @test startswith(sprint(show, h), "compose(")
  @test compose(id(dom(f)), f) == f
  @test compose(f, id(codom(f))) == f
end

# Constants.
#------------

c = SetFunction(ConstantFunction("foo", SetOb(Int)))
@test getvalue(c) isa ConstantFunction
@test dom(c) == SetOb(Int)
@test codom(c) == SetOb(String)
@test c(1) == "foo"

c = SetFunction(ConstantFunction(5, SetOb(Int)))

@withmodel SetC() (compose) begin 
  @test force(compose(c, f)) == SetFunction(ConstantFunction(f(5), SetOb(Int)))
  @test force(compose(f, c)) == c
  @test force(compose(c, c)) == c
end

# Predicated sets
#----------------

odds = PredicatedSet(Int, isodd) |> SetOb
evens = PredicatedSet(Int, iseven)  |> SetOb

plus_one_to_odd = SetFunction(x -> x+1, odds, evens)
plus_one_to_even = SetFunction(x -> x+1, evens, odds)

@test getvalue(plus_one_to_odd) isa PredicatedFunction

@test plus_one_to_odd(1) == 2
@test_throws ErrorException plus_one_to_odd(2) == 3
@test plus_one_to_even(2) == 3
@test_throws ErrorException plus_one_to_even(3) == 4
@test SetFunction(plus_one_to_odd) == plus_one_to_odd

plus_two_to_odd = compose[SetC()](plus_one_to_odd, plus_one_to_even)
@test plus_two_to_odd(3) == 5
@test dom(plus_two_to_odd) == odds
@test codom(plus_two_to_odd) == odds
@test_throws ErrorException plus_two_to_odd(2) == 4

end # module
