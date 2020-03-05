module LinearAlgebra

using Reexport

include("GLA.jl")

@reexport using .GraphicalLinearAlgebra

end
