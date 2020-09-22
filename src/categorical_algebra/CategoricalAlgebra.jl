module CategoricalAlgebra

using Reexport

include("CSets.jl")
include("Graphs.jl")
include("FreeDiagrams.jl")
include("Limits.jl")
include("FinSets.jl")
include("CSetMorphisms.jl")
include("Matrices.jl")
include("FinRelations.jl")
include("Permutations.jl")
include("PredicatedSets.jl")
include("StructuredCospans.jl")

@reexport using .FreeDiagrams
@reexport using .Limits
@reexport using .CSets
@reexport using .CSetMorphisms
@reexport using .StructuredCospans

end
