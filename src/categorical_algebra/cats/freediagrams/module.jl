module FreeDiagrams 
using Reexport 

include("FreeDiagrams.jl")

include("Discrete.jl")
@reexport using .Discrete

include("Multispans.jl")
@reexport using .Multispans

include("ParallelHoms.jl")
@reexport using .ParallelHoms

include("ComposableHoms.jl")
@reexport using .ComposableHoms

include("FreeGraphs.jl")
@reexport using .FreeGraphs

include("Bipartite.jl")
@reexport using .Bipartite

include("Specialize.jl")

end # module
