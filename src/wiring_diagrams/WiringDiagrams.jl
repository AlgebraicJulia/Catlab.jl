module WiringDiagrams

using Reexport

include("Core.jl")
include("Layers.jl")
include("Algorithms.jl")
include("Expressions.jl")
include("Serialization.jl")
include("GraphML.jl")
include("JSON.jl")

@reexport using .WiringDiagramCore
@reexport using .WiringLayers
@reexport using .WiringDiagramAlgorithms
@reexport using .WiringDiagramExpressions

using .WiringDiagramSerialization
export convert_from_graph_data, convert_to_graph_data

@reexport using .GraphMLWiringDiagrams
@reexport using .JSONWiringDiagrams

end
