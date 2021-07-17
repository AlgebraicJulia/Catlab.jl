module TestSubojects
using Test

using Catlab.CategoricalAlgebra, Catlab.CategoricalAlgebra.FinSets
using Catlab.Graphs

# Subsets
#########

X = FinSet(10)
A, B = FinFunction([1,2,5,6,8,9], X), FinFunction([2,3,5,7,8], X)
@test meet(A, B, SubobjectFromLimits()) |> force == FinFunction([2,5,8], X)
@test join(A, B, SubobjectFromLimits()) |> collect |> sort == [1,2,3,5,6,7,8,9]
@test bottom(X, SubobjectFromLimits()) == FinFunction(Int[], X)
@test top(X, SubobjectFromLimits()) |> force == FinFunction(1:10, X)

# Sub-C-sets
############

# Construct subobject.
g = path_graph(Graph, 4)
α = subobject(g, V=[2,3,4], E=[2,3])
@test is_natural(α)
@test dom(α) == path_graph(Graph, 3)
@test codom(α) == g

end
