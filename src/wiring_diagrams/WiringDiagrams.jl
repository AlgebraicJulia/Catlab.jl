module WiringDiagrams

using Reexport

include("Core.jl")
include("Layers.jl")
include("Algorithms.jl")
include("Serialization.jl")
include("GraphML.jl")
include("JSON.jl")

@reexport using .WiringDiagramCore
@reexport using .WiringLayers
@reexport using .WiringDiagramAlgorithms
@reexport using .GraphMLWiringDiagrams
@reexport using .JSONWiringDiagrams

end
