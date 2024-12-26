module CategoricalAlgebra

using Reexport

include("01_cats/module.jl") 
include("02_setcats/module.jl") # depends on Cats
include("03_csetcats/module.jl") # depends on Cats, SetCats
include("04_misc/module.jl") # doesn't depend on the other three

@reexport using .Cats
@reexport using .SetCats
@reexport using .CSetCats
@reexport using .Misc

end # module
