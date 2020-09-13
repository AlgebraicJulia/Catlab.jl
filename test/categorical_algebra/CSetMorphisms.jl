module TestCSetMorphisms
using Test

using Catlab, Catlab.CategoricalAlgebra, Catlab.CategoricalAlgebra.FinSets,
  Catlab.CategoricalAlgebra.Graphs
using Catlab.CategoricalAlgebra.Graphs: TheoryGraph

# C-set transformations
#######################

# C-sets
#-------

# Constructors and accessors
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

# Naturality
@test is_natural(α)
β = CSetTransformation((V=[1,2,1,2], E=[1,1,1]), g, h)
@test !is_natural(β)

# Attributed C-sets
#------------------

@present TheoryWeightedGraph <: TheoryGraph begin
  Weight::Data
  weight::Attr(E,Weight)
end
const WeightedGraph = ACSetType(TheoryWeightedGraph, index=[:src,:tgt])

# Constructors and accessors.
g, h = WeightedGraph{Float64}(2), WeightedGraph{Float64}(4)
add_edge!(g, 1, 2, weight=2.0)
add_edges!(h, [1,2,3], [2,3,4], weight=[1.0,2.0,3.0])
α = ACSetTransformation((V=[2,3], E=[2]), g, h)
@test length(components(α)) == 2

# Naturality.
@test is_natural(α)
β = ACSetTransformation((V=[2,1], E=[2]), g, h)
@test !is_natural(β) # Preserves weight but not graph homomorphism
β = ACSetTransformation((V=[1,2], E=[1]), g, h)
@test !is_natural(β) # Graph homomorphism but does not preserve weight

end
