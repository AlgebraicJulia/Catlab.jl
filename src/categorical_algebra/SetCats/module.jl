module SetCats 

using Reexport

include("SetCats.jl")
@reexport using .SetCats

include("FinSetCats.jl")
@reexport using .FinSetCats

include("VarFunctions.jl")
@reexport using .VarFunctions

end # module
