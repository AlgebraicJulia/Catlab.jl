module CategoricalAlgebra

using Reexport

include("cats/module.jl") 
@reexport using .Cats

include("setcats/module.jl") # depends on Cats
@reexport using .SetCats

include("pointwise/module.jl") # depends on Cats, SetCats
@reexport using .Pointwise

include("misc/module.jl") # doesn't depend on the other three

@reexport using .Misc

end # module
