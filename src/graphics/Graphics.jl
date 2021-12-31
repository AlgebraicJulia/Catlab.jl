module Graphics

using Reexport
using Requires

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

function __init__()
  @require Convex="f65535da-76fb-5f13-bab9-19810c17039a" begin
    @require SCS="c946c3f1-0d1f-5ce8-9dea-7daa1f7e2d13" begin
      include("ConvexExternal.jl")
    end
  end
  @require TikzPictures="37f6aa50-8035-52d0-81c2-5a1d08754b2d" begin
    include("TikZExternal.jl")
  end
end

end
