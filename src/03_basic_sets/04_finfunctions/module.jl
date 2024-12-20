module FinFunctions 

using Reexport

include("FinFunctions.jl")
include("FinFnVector.jl")
include("FinFnDict.jl")
include("FinForce.jl")

@reexport using .FinFnVector 
@reexport using .FinFnDict

end # module