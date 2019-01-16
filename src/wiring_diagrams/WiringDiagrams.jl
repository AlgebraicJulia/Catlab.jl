module WiringDiagrams

using Reexport

include("Core.jl")
include("Algorithms.jl")
include("GraphML.jl")

@reexport using .WiringDiagramCore
@reexport using .WiringDiagramAlgorithms
@reexport using .GraphMLWiringDiagrams

end
