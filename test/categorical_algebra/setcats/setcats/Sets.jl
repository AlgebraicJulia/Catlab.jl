module TestSets

using Test, Catlab

f = SetFunction(x -> 2x, TypeSet(Int), TypeSet(Int))
g = SetFunction(x -> 3x, TypeSet(Int), TypeSet(Int))

# Composition.
h = compose(f,g)
@test dom(h) == dom(f)
@test codom(h) == codom(g)
@test h(1) == 6
@test startswith(sprint(show, h), "compose(")
@test compose(id(dom(f)), f) == f
@test compose(f, id(codom(f))) == f

c = ConstantFunction(5, TypeSet(Int))
@test compose(c, f) == ConstantFunction(f(5), TypeSet(Int))
@test compose(f, c) == c
@test compose(c, c) == c

end # module
