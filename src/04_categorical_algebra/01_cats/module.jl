module Cats 

using Reexport

include("01_paths/Paths.jl") # [DEPS]
@reexport using .Paths

include("02_categories/module.jl") #
@reexport using .Categories

include("03_fincats/module.jl") # 2
@reexport using .FinCats

include("04_functors/module.jl") # 2
@reexport using .Functors

include("05_freediagrams/module.jl") # 3
@reexport using .FreeDiagrams

include("06_finfunctors/module.jl") # 2, 5
@reexport using .FinFunctors

include("07_cat_of_cat/CatOfCat.jl") # 2
@reexport using .CatOfCat

include("08_natural_transformations/module.jl")
@reexport using .NatTrans

include("09_limits_colimits/module.jl") # 4,5
@reexport using .LimitsColimits

include("10_commutative_diagrams/CommutativeDiagrams.jl")
@reexport using .CommutativeDiagrams

include("11_diagrams/module.jl") # 5
@reexport using .Diagrams

include("12_slice/SliceCategories.jl")
@reexport using .SliceCategories

include("13_subobjects/Subobjects.jl") # Limits
@reexport using .Subobjects

end # module
