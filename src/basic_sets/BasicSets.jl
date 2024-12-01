module BasicSets 

using Reexport

include("Sets.jl") # Categories
include("FinSets.jl") # Sets
include("SetFunctions.jl") # Sets, FinSets
include("FinFunctions.jl") # SetFunctions

@reexport using .Sets
@reexport using .FinSets
@reexport using .SetFunctions
@reexport using .FinFunctions

end # module
