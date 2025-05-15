module TestSetCCat 

using Catlab, Test

f = SetFunction(x -> 2x, SetOb(Int), SetOb(Int))
g = SetFunction(x -> 3x, SetOb(Int), SetOb(Int))
@test getvalue(f) isa CallableFunction
@test dom[SetC()](f) == SetOb(Int) == dom(f)
@test codom[SetC()](f) == SetOb(Int) == codom(f)
@test f(1) == 2

# Composition.
#-------------
f = SetFunction(x -> 2x, SetOb(Int), SetOb(Int))
g = SetFunction(x -> 3x, SetOb(Int), SetOb(Int))

@withmodel SetC() (id, compose) begin 
  h = compose(f,g)
  @test dom(h) == dom(f)
  @test codom(h) == codom(g)
  @test h(1) == 6
  @test startswith(sprint(show, h), "compose(")
  @test compose(id(dom(f)), f) == f
  @test compose(f, id(codom(f))) == f
end

end # module
