module SetCats

using Reexport

include("Sets.jl") # Categories
include("SetFunctions.jl") # Sets
include("FinSets.jl") # Sets
include("FinFunctions.jl") # SetFunctions

include("SetCLimits.jl") # SetFunctions
include("FinCLimits.jl") # Limits

include("Subsets.jl") # Subobjects, FinSets

include("GraphCategories.jl") # (not reexported)

@reexport using .Sets
@reexport using .SetFunctions
@reexport using .FinSets
@reexport using .FinFunctions
@reexport using .Subsets


end # module
