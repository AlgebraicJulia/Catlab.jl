""" Category of (possibly infinite) sets and functions.

This module defines generic types for the category of sets ([`SetOb`](@ref),
[`SetFunction`](@ref)), as well as a few basic concrete types, such as a wrapper
type to view Julia types as sets ([`TypeSet`](@ref)). Extensive support for
finite sets is provided by another module, [`FinSets`](@ref).
"""
module Sets

using Reexport 

include("Sets.jl")

include("TypeSets.jl")
@reexport using .TypeSets

include("PredSets.jl")
@reexport using .PredSets

end # module
