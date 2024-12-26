module FreeDiagrams 
using Reexport 

include("FreeDiagrams.jl")
include("Discrete.jl")
include("Multispans.jl")
include("ParallelHoms.jl")
include("ComposableHoms.jl")
include("FreeGraphs.jl")
include("Bipartite.jl")

@reexport using .Discrete
@reexport using .Multispans
@reexport using .ParallelHoms
@reexport using .ComposableHoms
@reexport using .FreeGraphs
@reexport using .Bipartite

end # module
