module CategoricalAlgebra

using Reexport

include("Categories.jl")
include("FinCats.jl")
include("FreeDiagrams.jl")
include("Limits.jl")
include("Subobjects.jl")
include("SetCats.jl")
include("FinSetCats.jl")
include("DiscreteCats.jl")
include("VarFunctions.jl")
include("Permutations.jl")
include("Matrices.jl")
include("FinRelations.jl")
include("Diagrams.jl")
include("CSets.jl")
include("HomSearch.jl")
include("GraphCategories.jl")
include("CommutativeDiagrams.jl")
include("CatElements.jl")
include("Chase.jl")
include("FunctorialDataMigrations.jl")
include("StructuredCospans.jl")
include("SliceCategories.jl")

@reexport using .Categories
@reexport using .FinCats
@reexport using .FreeDiagrams
@reexport using .Limits
@reexport using .Subobjects

@reexport using .SetCats
@reexport using .FinSetCats
@reexport using .DiscreteCats
@reexport using .VarFunctions
@reexport using .Permutations
@reexport using .CSets
@reexport using .HomSearch
@reexport using .CatElements

@reexport using .Diagrams
@reexport using .CommutativeDiagrams
@reexport using .Chase
@reexport using .FunctorialDataMigrations
@reexport using .StructuredCospans
@reexport using .SliceCategories

end
