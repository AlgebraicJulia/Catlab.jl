""" The category of finite sets and functions, and its skeleton.
"""
module FinSets

using Reexport

include("FinSets.jl")
include("FinSetInts.jl")
include("SingletonSets.jl")
include("EitherFinSet.jl")
include("TabularSet.jl")
include("FinSetHash.jl")
include("FinSetVect.jl")
include("SumFinSets.jl")
include("ProdFinSets.jl")

@reexport using .FinSetInts
@reexport using .SingletonSets
@reexport using .EitherFSet
@reexport using .TabSet
@reexport using .FSetHash
@reexport using .FSetVect
@reexport using .SumFinSets
@reexport using .ProdFinSets
end # module
