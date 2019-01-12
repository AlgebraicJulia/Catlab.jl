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
  @require TikzPictures="37f6aa50-8035-52d0-81c2-5a1d08754b2d" include("TikZExternal.jl")
end

end