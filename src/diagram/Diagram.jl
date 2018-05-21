module Diagram

using Reexport

include("Wiring.jl")
include("Algorithms.jl")
include("GraphML.jl")

include("Graphviz.jl")
include("GraphvizWiring.jl")
include("TikZ.jl")
include("TikZWiring.jl")
include("Interactive.jl")

@reexport using .Wiring
@reexport using .GraphML
@reexport using .GraphvizWiring
@reexport using .TikZWiring

end
