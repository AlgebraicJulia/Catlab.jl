module Graphics

using Reexport
using Requires

include("WiringDiagramLayouts.jl")
include("Graphviz.jl")
include("GraphvizWiringDiagrams.jl")
include("TikZ.jl")
include("TikZWiringDiagrams.jl")

@reexport using. WiringDiagramLayouts
@reexport using .GraphvizWiringDiagrams
@reexport using .TikZWiringDiagrams

function __init__()
  @require TikzPictures="37f6aa50-8035-52d0-81c2-5a1d08754b2d" include("TikZExternal.jl")
end

end
