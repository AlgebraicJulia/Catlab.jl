module SetCats

using Reexport

include("SkelFinSetCat/module.jl") # SetFunctions
@reexport using .SkelFinSetCat

include("FinSetCat/module.jl") # SetFunctions
@reexport using .FinSetCat


include("SetCat.jl") # SetFunctions
@reexport using .SetCat


include("CatsInterop.jl") # SetCat
@reexport using .CatsInterop

# include("FinCLimits.jl") # Limits
# include("Subsets.jl") # Subobjects, FinSets
# include("GraphCategories.jl") # (not reexported)

include("VarFunctions.jl")
@reexport using .VarFunctions

include("DiscreteCatLimits.jl") 

# @reexport using .Subsets


end # module
