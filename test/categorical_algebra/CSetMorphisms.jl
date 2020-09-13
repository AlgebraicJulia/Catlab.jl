module TestCSetMorphisms
using Test

using Catlab.CategoricalAlgebra, Catlab.CategoricalAlgebra.FinSets,
  Catlab.CategoricalAlgebra.Graphs

# Data structure
################

g, h = Graph(4), Graph(2)
add_edges!(g, [1,2,3], [2,3,4])
add_edges!(h, [1,2], [2,1])
α = CSetTransformation((V=[1,2,1,2], E=[1,2,1]), g, h)
@test components(α) == (V=α[:V], E=α[:E])
@test α[:V] isa FinFunction{Int} && α[:E] isa FinFunction{Int}
@test α[:V](3) == 1
@test α[:E](2) == 2
@test dom(α) === g
@test codom(α) === h

α′ = CSetTransformation(g, h, V=[1,2,1,2], E=[1,2,1])
@test components(α′) == components(α)
α′′ = CSetTransformation(g, h, V=FinFunction([1,2,1,2]), E=FinFunction([1,2,1]))
@test components(α′′) == components(α)

end
