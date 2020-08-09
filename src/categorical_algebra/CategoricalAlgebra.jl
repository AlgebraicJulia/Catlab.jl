module CategoricalAlgebra

using Reexport

include("CSets.jl")
include("Graphs.jl")
include("FreeDiagrams.jl")
include("Limits.jl")
include("Matrices.jl")
include("FinSets.jl")
include("FinRelations.jl")
include("Permutations.jl")
include("PredicatedSets.jl")

@reexport using .FreeDiagrams
@reexport using .Limits
@reexport using .CSets

end
