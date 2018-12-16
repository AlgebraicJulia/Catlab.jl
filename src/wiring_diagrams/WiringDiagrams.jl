module WiringDiagrams

using Reexport

include("Core.jl")
include("Algorithms.jl")
include("GraphML.jl")

@reexport using .WiringCore
@reexport using .WiringAlgorithms
@reexport using .GraphML

end
