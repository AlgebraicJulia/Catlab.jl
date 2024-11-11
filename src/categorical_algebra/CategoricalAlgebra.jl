module CategoricalAlgebra

using Reexport

include("BasicSets/BasicSets.jl") # 
include("Cats/Cats.jl") # depends on BasicSets
include("SetCats/SetCats.jl") # depends on Cats
# include("CSetCats/CSetCats.jl") # depends on SetCats
include("Misc/Misc.jl") # doesn't depend on the other three

@reexport using .BasicSets
@reexport using .Cats
@reexport using .SetCats
# @reexport using .CSetCats
@reexport using .Misc

end # module
