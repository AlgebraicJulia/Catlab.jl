""" 
This module defines generic types for the category of sets ([`SetOb`](@ref),
[`SetFunction`](@ref)), as well as a few basic concrete types, such as a wrapper
type to view Julia types as sets ([`TypeSet`](@ref)). Extensive support for
finite sets is provided by another module, [`FinSets`](@ref).
"""
module Sets 
using Reexport 
include("Sets.jl")
include("TypeSet.jl")
include("UnionSet.jl")
include("EitherSets.jl")
include("PredSet.jl")
include("SumSets.jl")
include("ProdSets.jl")

@reexport using .Sets
@reexport using .TypeSets
@reexport using .UnionSets
@reexport using .EitherSets
@reexport using .PredSets
@reexport using .SumSets
@reexport using .ProdSets

end # module
