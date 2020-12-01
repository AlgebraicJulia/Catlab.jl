module LinearAlgebra

using Reexport

include("TensorNetworks.jl")
include("GLA.jl")
include("StructuredGLA.jl")

@reexport using .TensorNetworks
@reexport using .GraphicalLinearAlgebra
@reexport using .StructuredGraphicalLinearAlgebra

end
