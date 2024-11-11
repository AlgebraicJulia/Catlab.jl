""" The category of finite sets and functions, and its skeleton.
"""
module FinSets
export FinSet

using GATlab
import GATlab: getvalue
using StructEquality
using Reexport

using ..Sets, ..SetFunctions
using ..Sets: ThSet′, SetImpl
import ..Sets: SetOb, left, right

import ....Theories: Ob

# Theory of FinSets
###################

"""
Any finite set must satisfy the interface of `ThSet′` in addition to providing 
Julia's interator interface and having a integer cardinality, i.e. `length`.
"""
@theory ThFinSet <: ThSet′ begin
  Int′::TYPE
  length′()::Int′
  iterate′()::Any′
  iterate′(a::Any′)::Any′
end

""" Any type which subtypes FinSetImpl is expected to implement ThFinSet """
abstract type FinSetImpl <: Model{Tuple{Bool, Any, Int}} end 

# Wrapper type for Models of ThFinSet
#####################################

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

# Access model methods
#---------------------

Base.in(e, f::FinSet) = ThFinSet.in′[getvalue(f)](e)

Base.eltype(s::FinSet) = ThFinSet.eltype′[getvalue(s)]()

Base.length(f::FinSet) = ThFinSet.length′[getvalue(f)]()

Base.iterate(f::FinSet, args...) = 
  ThFinSet.iterate′[getvalue(f)](args...)


# Other methods 
#--------------

FinSet(set::FinSet) = set # no-op

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
include("FinSetImpls/FinSetVect.jl")

@reexport using .FSetInt
@reexport using .EitherFSet
@reexport using .TabSet
@reexport using .FSetHash
@reexport using .FSetVect


end # module
