module Cats 

using Reexport

include("Paths.jl") # (no deps)

include("Categories.jl") # (no deps)

include("Functors.jl") # Categories

include("NatTrans.jl") # Categories

include("CatImpls/CatofCat.jl") # Categories

include("FreeDiagrams.jl") # FinCats

include("CommutativeDiagrams.jl")

include("Limits.jl") # FreeDiagrams

include("Subobjects.jl") # Limits


include("FinFunctors.jl") # Categories, FreeDiagrams

include("CatImpls/FinCatCat.jl") # FinFunctors

# include("SliceCategories.jl")

# Maybe this needs to come after everything else?
# include("Diagrams.jl") # Categories, Limits, FinCats, FinSets

@reexport using .Paths
@reexport using .Categories
@reexport using .Functors
@reexport using .NatTrans
@reexport using .CatOfCat
@reexport using .FreeDiagrams
@reexport using .CommutativeDiagrams
@reexport using .Limits
@reexport using .Subobjects
@reexport using .FinFunctors
@reexport using .FinCatCat

# @reexport using .Diagrams
# @reexport using .SliceCategories

end # module