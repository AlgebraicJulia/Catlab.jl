""" The category of finite sets and functions, and its skeleton.
"""
module FinSets
export FinSet, FinSetInt, FinSetHash, TabularSet

using GATlab
import GATlab: getvalue
using StructEquality
using Reexport
import Tables, PrettyTables

using ..Sets, ..SetFunctions
using ..Sets: ThSet′, SetImpl
import ..Sets: SetOb, left, right

import ....Theories: Ob

# Theory of FinSets
###################

@theory ThFinSet <: ThSet′ begin
  Int′::TYPE
  length′()::Int′
  iterate′()::Any′
  iterate′(a::Any′)::Any′
end

abstract type FinSetImpl <: Model{Tuple{Bool, Any, Int}} end 

""" Finite set.

A finite set has abstract type `FinSet{S,T}`. The second type parameter `T` is
the element type of the set and the first parameter `S` is the collection type,
which can be a subtype of `AbstractSet` or another Julia collection type. In
addition, the skeleton of the category **FinSet** is the important special case
`S = Int`. The set ``{1,…,n}`` is represented by the object `FinSet(n)` of type
`FinSet{Int,Int}`.
"""
@struct_hash_equal struct FinSet <: AbsSet
  impl::FinSetImpl
  FinSet(i::FinSetImpl) = implements(i, ThFinSet) ? new(i) : throw(MethodError(
    "Bad model $i"))
end

getvalue(f::FinSet) = f.impl

Base.in(e, f::FinSet) = ThFinSet.in′[getvalue(f)](e)

Base.length(f::FinSet) = ThFinSet.length′[getvalue(f)]()

Base.iterate(f::FinSet, args...) = 
  ThFinSet.iterate′[getvalue(f)](args...)

Base.eltype(s::FinSet) = ThFinSet.eltype′[getvalue(s)]()

# Normally we would have to migrate the model, but because the sorts are the 
# same between the two theories, this is unnecessary.
""" Explicitly cast FinSet as SetOb. This will always succeed. """
# SetOb(f::FinSet) = SetOb(f.impl, getmodel(f)) # migrate_model(ι, f.mod)) 

""" Attempt to cast SetOb to FinSet ... this can throw runtime error."""
# FinSet(s::SetOb) = FinSet(s.impl, s.mod) 

FinSet(set::FinSet) = set

Base.show(io::IO, set::FinSet) = show(io, getvalue(set))

Base.show(io::IO, mime::MIME"text/plain", set::FinSet) = 
  show(io, mime, getvalue(set))

Base.show(io::IO, mime::MIME"text/html", set::FinSet) = 
  show(io, mime, getvalue(set))

# Implementations
#################
include("FinSetImpls/FinSetInt.jl")

include("FinSetImpls/EitherFinSet.jl")

include("FinSetImpls/TabularSet.jl")

include("FinSetImpls/FinSetHash.jl")

end # module
