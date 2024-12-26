""" Categories of C-sets and attributed C-sets.
"""
module CSets
using Reexport

include("Heteromorphisms.jl")
@reexport using .Heteromorphisms

include("CSets.jl")

include("CollageCats.jl")
@reexport using .CollageCats

include("ACSetFunctors.jl")
@reexport using .ACSetFunctors


end # module