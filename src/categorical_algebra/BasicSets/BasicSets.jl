module BasicSets 

using Reexport

include("Sets.jl") # Categories
include("SetFunctions.jl") # Sets
include("FinSets.jl") # Sets
include("FinFunctions.jl") # SetFunctions

@reexport using .Sets
@reexport using .SetFunctions
@reexport using .FinSets
@reexport using .FinFunctions

end # module
