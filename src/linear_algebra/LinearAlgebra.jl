module LinearAlgebra

using Reexport

include("GLA.jl")
include("StructuredGLA.jl")

@reexport using .GraphicalLinearAlgebra
@reexport using .StructuredGraphicalLinearAlgebra

end
