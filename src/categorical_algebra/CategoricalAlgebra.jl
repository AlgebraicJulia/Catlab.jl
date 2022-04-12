module CategoricalAlgebra

using Reexport

include("Categories.jl")
include("FinCats.jl")
include("FreeDiagrams.jl")
include("Limits.jl")
include("Subobjects.jl")
include("Sets.jl")
include("FinSets.jl")
include("Matrices.jl")
include("FinRelations.jl")
include("CSets.jl")
include("GraphCategories.jl")
include("Chase.jl")
include("Diagrams.jl")
include("CommutativeDiagrams.jl")
include("CatElements.jl")
include("DataMigrations.jl")
include("StructuredCospans.jl")
include("DPO.jl")
include("Slices.jl")

@reexport using .Categories
@reexport using .FinCats
@reexport using .FreeDiagrams
@reexport using .Limits
@reexport using .Subobjects

@reexport using .Sets
@reexport using .FinSets
@reexport using .CSets
@reexport using .CatElements

@reexport using .Chase
@reexport using .Diagrams
@reexport using .CommutativeDiagrams
@reexport using .DataMigrations
@reexport using .StructuredCospans
@reexport using .DPO
@reexport using .Slices

end
