module SetCats

using Reexport


include("CatsInterop.jl") # SetFunctions
include("SetCLimits.jl") # SetFunctions
include("FinCLimits.jl") # Limits
include("Subsets.jl") # Subobjects, FinSets
include("GraphCategories.jl") # (not reexported)
include("VarFunctions.jl") # (not reexported)

@reexport using .Subsets
@reexport using .VarFunctions


end # module
