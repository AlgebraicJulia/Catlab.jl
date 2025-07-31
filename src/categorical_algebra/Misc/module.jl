module Misc 

using Reexport

include("Permutations.jl") # (no deps)
include("Matrices.jl") # (no deps, not reexported)
include("FinRelations.jl") # (Matrices, not reexported)

@reexport using .Permutations

end # module 
