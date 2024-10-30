module Cats 

using Reexport

include("Categories.jl") # (no deps)

include("FreeDiagrams.jl") # FinCats

include("CommutativeDiagrams.jl")

include("Limits.jl") # FreeDiagrams

include("Subobjects.jl") # Limits

include("FinCats.jl") # Categories, FreeDiagrams

include("FinFunctors.jl") # Categories, FreeDiagrams

# include("SliceCategories.jl")

# Maybe this needs to come after everything else?
# include("Diagrams.jl") # Categories, Limits, FinCats, FinSets

@reexport using .Categories
@reexport using .FreeDiagrams
@reexport using .CommutativeDiagrams
@reexport using .Limits
@reexport using .Subobjects
@reexport using .FinCats
@reexport using .FinFunctors

# @reexport using .Diagrams
# @reexport using .SliceCategories

end # module
