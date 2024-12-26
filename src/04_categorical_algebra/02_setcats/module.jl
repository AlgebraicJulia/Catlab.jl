module SetCats

using Reexport

include("SkelFinSetCat.jl") # SetFunctions
@reexport using .SkelFinSetCat

include("SetCat.jl") # SetFunctions
@reexport using .SetCat


# include("CatsInterop.jl") # SetFunctions
# include("FinCLimits.jl") # Limits
# include("Subsets.jl") # Subobjects, FinSets
# include("GraphCategories.jl") # (not reexported)

include("VarFunctions.jl")
@reexport using .VarFunctions

include("DiscreteCatLimits.jl") 

# @reexport using .CatsInterop
# @reexport using .Subsets


end # module
