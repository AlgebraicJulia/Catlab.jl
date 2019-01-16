module WiringDiagrams

using Reexport

include("Core.jl")
include("Algorithms.jl")
include("GraphML.jl")
include("JSON.jl")

@reexport using .WiringDiagramCore
@reexport using .WiringDiagramAlgorithms
@reexport using .GraphMLWiringDiagrams
@reexport using .JSONWiringDiagrams

end
