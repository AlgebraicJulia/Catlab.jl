module WiringDiagrams

using Reexport

include("Directed.jl")
include("Undirected.jl")
include("MonoidalDirected.jl")
include("MonoidalUndirected.jl")
include("Algebras.jl")
include("Algorithms.jl")
include("Expressions.jl")
include("ScheduleUndirected.jl")

@reexport using .DirectedWiringDiagrams
@reexport using .UndirectedWiringDiagrams
@reexport using .MonoidalDirectedWiringDiagrams
@reexport using .MonoidalUndirectedWiringDiagrams
@reexport using .WiringDiagramAlgebras
@reexport using .WiringDiagramAlgorithms
@reexport using .WiringDiagramExpressions
@reexport using .ScheduleUndirectedWiringDiagrams

include("Serialization.jl")
include("GraphML.jl")
include("JSON.jl")

using .WiringDiagramSerialization
export convert_from_graph_data, convert_to_graph_data
@reexport using .GraphMLWiringDiagrams
@reexport using .JSONWiringDiagrams

end
