module SetCats 

using Reexport

include("SetCat/module.jl")
@reexport using .SetCat

include("FinSetCats/module.jl")
@reexport using .FinSetCats

include("SkelFinSetCat/module.jl")
@reexport using .SetCats

include("VarFunctions/module.jl")
@reexport using .VarFunctions

include("GraphCategories.jl")

include("Subsets.jl")
@reexport using .Subsets

end # module
