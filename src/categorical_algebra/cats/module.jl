module Cats 

using Reexport

include("Paths.jl")
@reexport using .Paths

include("categories/module.jl")
@reexport using .Categories

include("fincats/module.jl") 
@reexport using .FinCats

include("functors/module.jl") 
@reexport using .Functors

include("freediagrams/module.jl")
@reexport using .FreeDiagrams

include("finfunctors/module.jl") 
@reexport using .FinFunctors

include("CatOfCat.jl")
@reexport using .CatOfCat

include("natural_transformations/module.jl")
@reexport using .Transformations

include("limits_colimits/module.jl") 
@reexport using .LimitsColimits

include("CommutativeDiagrams.jl")
@reexport using .CommutativeDiagrams

include("diagrams/module.jl")
@reexport using .Diagrams

include("slice/module.jl")
@reexport using .SliceCategories

include("Subobjects.jl")
@reexport using .Subobjects

end # module
