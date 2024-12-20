module SetCats

using Reexport

include("SkelFinSetCat.jl") # SetFunctions
@reexport using .SkelFinSetCat

# include("CatsInterop.jl") # SetFunctions
# include("FinCLimits.jl") # Limits
# include("Subsets.jl") # Subobjects, FinSets
# include("GraphCategories.jl") # (not reexported)

include("VarFunctions.jl") # (not reexported)
@reexport using .VarFunctions

# @reexport using .CatsInterop
# @reexport using .Subsets


end # module
