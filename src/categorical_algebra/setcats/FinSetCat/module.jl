module FinSetCat

using Reexport

include("FinSetCat.jl")

include("Limits.jl")
@reexport using .FinSetCatLimits

include("Colimits.jl")
@reexport using .FinSetCatColimits

end # module
