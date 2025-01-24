""" Free diagrams in a category.

A [free diagram](https://ncatlab.org/nlab/show/free+diagram) in a category is a
diagram whose shape is a free category. Examples include the empty diagram,
pairs of objects, discrete diagrams, parallel pairs, composable pairs, and spans
and cospans. Limits and colimits are most commonly taken over free diagrams.
"""
module FreeDiagrams

using Reexport

include("FreeDiagrams.jl")

include("Discrete.jl")
@reexport using .Discrete

include("Multispans.jl")
@reexport using .Multispans

include("ComposableHoms.jl")
@reexport using .ComposableHoms

include("ParallelHoms.jl")
@reexport using .ParallelHoms

include("Bipartite.jl")
@reexport using .Bipartite

include("FreeGraphs.jl")
@reexport using .FreeGraphs

end # module