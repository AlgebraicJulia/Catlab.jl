module FinFunctions 
using Reexport

include("FinFunctions.jl")

include("FinFnVector.jl")
@reexport using .FinFnVector

include("FinFnDict.jl")
@reexport using .FinFnDict

include("FinForce.jl")

end # module 