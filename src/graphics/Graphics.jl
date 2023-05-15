module Graphics

using Reexport

include("WiringDiagramLayouts.jl")
include("Graphviz.jl")
include("GraphvizGraphs.jl")
include("GraphvizWiringDiagrams.jl")
include("GraphvizCategories.jl")
include("ComposeWiringDiagrams.jl")
include("TikZ.jl")
include("TikZWiringDiagrams.jl")

@reexport using .WiringDiagramLayouts
@reexport using .GraphvizGraphs
@reexport using .GraphvizWiringDiagrams
@reexport using .GraphvizCategories
@reexport using .ComposeWiringDiagrams
@reexport using .TikZWiringDiagrams

end
