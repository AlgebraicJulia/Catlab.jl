module CategoricalAlgebra

using Reexport

include("Cats/Cats.jl") 
include("SetCats/SetCats.jl") # depends on Cats
include("CSetCats/CSetCats.jl") # depends on SetCats
include("Misc/Misc.jl") # doesn't depend on the other three

@reexport using .Cats
@reexport using .SetCats
@reexport using .CSetCats
@reexport using .Misc

end # module
