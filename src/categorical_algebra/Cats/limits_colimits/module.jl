""" Limits and colimits in a category.
"""
module LimitsColimits
using Reexport 

include("LimitsColimits.jl")

include("Limits.jl")
@reexport using .Limits

include("Colimits.jl")
@reexport using .Colimits

include("Singletons.jl")
@reexport using .Singletons

include("Terminals.jl")
@reexport using .Terminals
include("Products.jl")
@reexport using .Products
include("Equalizers.jl")
@reexport using .Equalizers
include("Pullbacks.jl")
@reexport using .Pullbacks
include("MonoidalLimits.jl")
@reexport using .MonoidalLimits

include("Initials.jl")
@reexport using .Initials
include("Coproducts.jl")
@reexport using .Coproducts
include("Coequalizers.jl")
@reexport using .Coequalizers
include("Pushouts.jl")
@reexport using .Pushouts
include("MonoidalColimits.jl")
@reexport using .MonoidalColimits

include("FreeGraphs.jl")
@reexport using .FreeGraphs

include("EpiMono.jl")
@reexport using .EpiMono


end # module
