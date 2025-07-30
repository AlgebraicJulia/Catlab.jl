module FinFunctors 

using Reexport

include("FinFunctors.jl")

include("FinDomMap.jl")
@reexport using .FinDomMap

end # module
