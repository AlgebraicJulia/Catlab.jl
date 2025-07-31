module SetCats

using Reexport

include("skelfinsetcat/module.jl") 
@reexport using .SkelFinSetCat

include("finsetcat/module.jl") 
@reexport using .FinSetCat

include("setcat/module.jl") 
@reexport using .SetCat

include("CatsInterop.jl")
@reexport using .CatsInterop

include("Subsets.jl") 
@reexport using .Subsets

include("varfunctions/module.jl")
@reexport using .VarFunctions

include("GraphCategories.jl") # (not reexported)

include("DiscreteCatLimits.jl") # nothing to reexport

end # module
