""" The category of finite sets and functions, and its skeleton.
"""
module FinSets

using Reexport

include("FinSets.jl")

include("ProdFinSets.jl")
@reexport using .ProdFinSets

include("FinSetsAsSets.jl")
@reexport using .FinSetsAsSets

include("FinSetInts.jl")
@reexport using .FinSetInts

include("SingletonSets.jl")
@reexport using .SingletonSets

include("EmptySets.jl")
@reexport using .EmptySets

include("EitherFinSet.jl")
@reexport using .EitherFSet

include("TabularSet.jl")
@reexport using .TabSet

include("FinSetHash.jl")
@reexport using .FSetHash

include("FinSetVect.jl")
@reexport using .FSetVect

include("SumFinSets.jl")
@reexport using .SumFinSets

include("PredicatedFinsets.jl")
@reexport using .PredFinSets

end # module
