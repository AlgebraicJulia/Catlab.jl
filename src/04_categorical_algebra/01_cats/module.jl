module Cats 

using Reexport

include("01_paths/Paths.jl") #
@reexport using .Paths

include("02_categories/module.jl") #
@reexport using .Categories

include("03_fincats/module.jl") # 2
@reexport using .FinCats

include("04_functors/module.jl") # 2
@reexport using .Functors

include("05_freediagrams/module.jl") # 3
@reexport using .FreeDiagrams

include("06_finfunctors/module.jl") # Categories, FreeDiagrams
@reexport using .FinFunctors

# include("NatTrans.jl") # Categories

include("07_cat_of_cat/CatOfCat.jl") # Categories
@reexport using .CatOfCat


include("08_diagrams/Diagrams.jl") # Categories, Limits, FinCats, FinSets
@reexport using .Diagrams

include("09_limits_colimits/module.jl") # FreeDiagrams, FinFunctors

@reexport using .LimitsColimits

include("10_commutative_diagrams/CommutativeDiagrams.jl")

@reexport using .CommutativeDiagrams

# include("Subobjects.jl") # Limits

# include("CatImpls/FinCatCat.jl") # FinFunctors

# include("SliceCategories.jl")



end # module
