module BasicSets 

using Reexport

include("01_sets/module.jl") # Categories
include("02_finsets/module.jl") # 1
include("03_setfunctions/module.jl") # 2
include("04_finfunctions/module.jl") # 3

@reexport using .Sets
@reexport using .FinSets
@reexport using .SetFunctions
@reexport using .FinFunctions

end # module
