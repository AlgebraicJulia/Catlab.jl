module CategoricalAlgebra

using Reexport

include("FreeDiagrams.jl")
include("Limits.jl")
include("FinSets.jl")
include("Matrices.jl")
include("FinRelations.jl")
include("PredicatedSets.jl")
include("CSets.jl")
include("GraphCategories.jl")
include("StructuredCospans.jl")
include("Squares.jl")

@reexport using .FreeDiagrams
@reexport using .Limits
@reexport using .CSets
@reexport using .StructuredCospans
@reexport using .Squares

end
