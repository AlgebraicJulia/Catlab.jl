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

end
