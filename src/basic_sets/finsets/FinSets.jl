export FinSet

using GATlab
import GATlab: getvalue
using StructEquality

using ..Sets
using ..Sets: ThSet′
import ..Sets: SetOb, left, right

import ....Theories: Ob
import Base: length, iterate

# Theory of FinSets
###################

"""
Any finite set must satisfy the interface of `ThSet′` in addition to providing 
Julia's iterator interface and having a integer cardinality, i.e. `length`.
"""
@theory ThFinSet <: ThSet′ begin
  Int′::TYPE
  length()::Int′
  iterate()::Any′
  iterate(a::Any′)::Any′
end

# Wrapper type for Models of ThFinSet
#####################################
import .ThFinSet.Meta

""" Finite set.

A finite set has abstract type `FinSet{S,T}`. The second type parameter `T` is
the element type of the set and the first parameter `S` is the collection type,
which can be a subtype of `AbstractSet` or another Julia collection type. In
addition, the skeleton of the category **FinSet** is the important special case
`S = Int`. The set ``{1,…,n}`` is represented by the object `FinSet(n)` of type
`FinSet{Int,Int}`.
"""
ThFinSet.Meta.@wrapper FinSet <: AbsSet

FinSet(set::FinSet) = set # no-op

Base.show(io::IO, set::FinSet) = show(io, getvalue(set))

Base.show(io::IO, mime::MIME"text/plain", set::FinSet) = 
  show(io, mime, getvalue(set))

Base.show(io::IO, mime::MIME"text/html", set::FinSet) = 
  show(io, mime, getvalue(set))

