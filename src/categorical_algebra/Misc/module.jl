module Misc 
using Reexport

include("Permutations.jl")
include("Matrices.jl")
include("FinRelations.jl")

@reexport using .Permutations

end # module
