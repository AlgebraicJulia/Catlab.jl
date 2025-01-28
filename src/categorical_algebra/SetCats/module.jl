module SetCats

using Reexport

include("SkelFinSetCat/module.jl") 
@reexport using .SkelFinSetCat

include("FinSetCat/module.jl") 
@reexport using .FinSetCat

include("SetCat/module.jl") 
@reexport using .SetCat

include("CatsInterop.jl")
@reexport using .CatsInterop

include("Subsets.jl") 
@reexport using .Subsets

include("VarFunctions/module.jl")
@reexport using .VarFunctions

include("GraphCategories.jl") # (not reexported)

include("DiscreteCatLimits.jl") # nothing to reexport

end # module
