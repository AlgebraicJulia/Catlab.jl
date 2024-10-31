""" Category of (possibly infinite) sets and functions.

This module defines generic types for the category of sets ([`SetOb`](@ref),
[`SetFunction`](@ref)), as well as a few basic concrete types, such as a wrapper
type to view Julia types as sets ([`TypeSet`](@ref)). Extensive support for
finite sets is provided by another module, [`FinSets`](@ref).
"""
module Sets
export AbsSet, SetOb, TypeSet, PredicatedSet, EitherSet, left, right

using StructEquality

using GATlab

# Theory of Sets
################

@theory ThSet′ begin
  Bool′::TYPE
  Any′::TYPE
  in′(e::Any′)::Bool′
  eltype′()::Any′
end

abstract type AbsSet end

abstract type SetImpl <: Model{Tuple{Bool, Any}} end 

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

Base.in(e, s::SetOb) = ThSet′.in′[getvalue(s)](e)

Base.eltype(s::SetOb) = ThSet′.eltype′[getvalue(s)]()

Base.show(io::IO, s::SetOb) = show(io, getvalue(s))


# Implementations
#################

include("SetImpls/TypeSet.jl")

include("SetImpls/EitherSet.jl")

include("SetImpls/PredSet.jl")

end # module
