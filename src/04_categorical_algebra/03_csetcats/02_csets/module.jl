""" Categories of C-sets and attributed C-sets.
"""
module CSets
using Reexport

include("CSets.jl")

include("CodomsOfACSet.jl")
@reexport using .CodomsOfACSet

include("ACSetFunctors.jl")
@reexport using .ACSetFunctors


end # module