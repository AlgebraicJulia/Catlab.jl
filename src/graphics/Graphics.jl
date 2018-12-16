module Graphics

using Reexport
using Requires

include("Graphviz.jl")
include("GraphvizWiring.jl")
include("TikZ.jl")
include("TikZWiring.jl")

@reexport using .GraphvizWiring
@reexport using .TikZWiring

function __init__()
  @require GraphViz="16d363e1-28f1-5f2b-b949-57f6f2d5f8ba" include("GraphvizExternal.jl")
  @require TikzPictures="37f6aa50-8035-52d0-81c2-5a1d08754b2d" include("TikZExternal.jl")
end

end