""" Category of (possibly infinite) sets and functions.

This module defines generic types for the category of sets ([`SetOb`](@ref),
[`SetFunction`](@ref)), as well as a few basic concrete types, such as a wrapper
type to view Julia types as sets ([`TypeSet`](@ref)). Extensive support for
finite sets is provided by another module, [`FinSets`](@ref).
"""
module Sets
export AbsSet, SetOb

using StructEquality
using Reexport

using GATlab

# Theory of Sets
################

"""
One ought be able to ask of any Set whether something is in it. Also a Julia 
type should be provided which includes all elements of the set.
"""
@theory ThSet′ begin
  Bool′::TYPE
  Any′::TYPE
  in′(e::Any′)::Bool′
  eltype′()::Any′
end

""" There are two kinds of Abstract Set. `SetOb` and `FinSet`."""
abstract type AbsSet end

""" Any type which subtypes SetImpl should implement `ThSet′`. """
abstract type SetImpl <: Model{Tuple{Bool, Any}} end 

# Wrapper type for Models of ThSet′
##################################
"""
Generic type for a set. It has some implementation of the theory of sets and 
a model which provides the information for how it implements the theory.
"""
@struct_hash_equal struct SetOb <: AbsSet
  impl::SetImpl
  SetOb(i::SetImpl) = implements(i, ThSet′) ? new(i) : throw(MethodError(
    "Bad model $i"))
end

GATlab.getvalue(s::SetOb) = s.impl

# Access the model methods
#-------------------------

Base.in(e, s::SetOb) = ThSet′.in′[getvalue(s)](e)

Base.eltype(s::SetOb) = ThSet′.eltype′[getvalue(s)]()

# Other methods 
#--------------

Base.show(io::IO, s::SetOb) = show(io, getvalue(s))

# Implementations
#################

include("SetImpls/TypeSet.jl")
include("SetImpls/EitherSet.jl")
include("SetImpls/PredSet.jl")

@reexport using .TypeSets
@reexport using .EitherSets
@reexport using .PredSets


end # module
