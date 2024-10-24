module CategoricalAlgebra

using Reexport


include("Matrices.jl") # (no deps, not reexported)
include("Permutations.jl") # (no deps)
include("Categories.jl") # (no deps)
include("FreeDiagrams.jl") # FinCats


include("FinRelations.jl") # Matrices


include("Limits.jl") # FreeDiagrams


include("FinCats.jl") # Categories, FreeDiagrams
include("Subobjects.jl") # LimitsOld


include("Sets.jl") # Categories
include("SetFunctions.jl") # Sets
include("FinSets.jl") # Sets
include("FinFunctions.jl") # SetFunctions

include("SetCLimits.jl") # 
include("FinCLimits.jl") # Limits

include("Subsets.jl") # Subobjects, FinSets



# include("Diagrams.jl") # Categories, Limits, FinCats, FinSets

# include("CSets.jl")

# include("HomSearch.jl")
include("GraphCategories.jl")
# include("CommutativeDiagrams.jl")
# include("CatElements.jl")
# include("Chase.jl")
# include("FunctorialDataMigrations.jl")
# include("StructuredCospans.jl")
# include("SliceCategories.jl")

@reexport using .Permutations
@reexport using .Categories

@reexport using .FinCats
@reexport using .FreeDiagrams
@reexport using .Limits
@reexport using .Subobjects

@reexport using .Sets
@reexport using .SetFunctions
@reexport using .FinSets
@reexport using .FinFunctions
@reexport using .Subsets

# @reexport using .CSets
# @reexport using .HomSearch
# @reexport using .CatElements

# @reexport using .Diagrams
# @reexport using .CommutativeDiagrams
# @reexport using .Chase
# @reexport using .FunctorialDataMigrations
# @reexport using .StructuredCospans
# @reexport using .SliceCategories

end
