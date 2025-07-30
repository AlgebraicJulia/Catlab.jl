module CategoricalAlgebra

using Reexport

include("Cats/module.jl")
@reexport using .Cats

include("SetCats/module.jl")
@reexport using .SetCats

include("Pointwise/module.jl")
@reexport using .Pointwise

include("Misc/module.jl")
@reexport using .Misc

end # module
