module WiringDiagrams

using Reexport

include("Directed.jl")
include("Undirected.jl")
include("MonoidalDirected.jl")
include("MonoidalUndirected.jl")
include("Algorithms.jl")
include("Expressions.jl")
include("Serialization.jl")
include("GraphML.jl")
include("JSON.jl")

@reexport using .DirectedWiringDiagrams
@reexport using .UndirectedWiringDiagrams
@reexport using .MonoidalDirectedWiringDiagrams
@reexport using .MonoidalUndirectedWiringDiagrams
@reexport using .WiringDiagramAlgorithms
@reexport using .WiringDiagramExpressions

using .WiringDiagramSerialization
export convert_from_graph_data, convert_to_graph_data
@reexport using .GraphMLWiringDiagrams
@reexport using .JSONWiringDiagrams

end
