""" The category of finite sets and functions, and its skeleton.
"""
module FinSets

using Reexport 

include("FinSets.jl")

include("FinSetInts.jl")
@reexport using .FinSetInts

include("FinSetHash.jl")
@reexport using .FinSetHash

include("TabularSets.jl")
@reexport using .TabularSets

end # module