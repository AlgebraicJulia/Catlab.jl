module CategoricalAlgebra

using Reexport

include("FreeDiagrams.jl")
include("Limits.jl")
include("Subobjects.jl")
include("Sets.jl")
include("FinSets.jl")
include("Matrices.jl")
include("FinRelations.jl")
include("CSets.jl")
include("Categories.jl")
include("FinCats.jl")
include("GraphCategories.jl")
include("StructuredCospans.jl")
include("CommutativeDiagrams.jl")
include("CatElements.jl")
include("DataMigration.jl")
include("DPO.jl")

@reexport using .FreeDiagrams
@reexport using .CommutativeDiagrams
@reexport using .Limits
@reexport using .Subobjects

@reexport using .Sets
@reexport using .FinSets
@reexport using .CSets
@reexport using .Categories
@reexport using .FinCats

@reexport using .StructuredCospans
@reexport using .CatElements
@reexport using .DataMigration
@reexport using .DPO

end
