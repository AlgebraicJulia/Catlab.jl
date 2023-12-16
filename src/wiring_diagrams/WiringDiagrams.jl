module WiringDiagrams

using Reexport

include("Directed.jl")
include("CPortGraphs.jl")
include("Undirected.jl")
include("MonoidalDirected.jl")
include("MonoidalUndirected.jl")
include("Algebras.jl")
include("Algorithms.jl")
include("Expressions.jl")

@reexport using .DirectedWiringDiagrams
@reexport using .CPortGraphs
@reexport using .UndirectedWiringDiagrams
@reexport using .MonoidalDirectedWiringDiagrams
@reexport using .MonoidalUndirectedWiringDiagrams
@reexport using .WiringDiagramAlgebras
@reexport using .WiringDiagramAlgorithms
@reexport using .WiringDiagramExpressions

include("Serialization.jl")
include("GraphML.jl")
include("JSON.jl")

using .WiringDiagramSerialization
export convert_from_graph_data, convert_to_graph_data
@reexport using .GraphMLWiringDiagrams
@reexport using .JSONWiringDiagrams

end
