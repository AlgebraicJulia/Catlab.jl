export FinSet

using StructEquality
import StaticArrays

using ACSets
using ..Sets

# Finite sets
#############

""" Finite set.

A finite set has abstract type `FinSet{S,T}`. The second type parameter `T` is
the element type of the set and the first parameter `S` is the collection type,
which can be a subtype of `AbstractSet` or another Julia collection type. In
addition, the skeleton of the category **FinSet** is the important special case
`S = Int`. The set ``{1,…,n}`` is represented by the object `FinSet(n)` of type
`FinSet{Int,Int}`.
"""
abstract type FinSet{S,T} <: SetOb{T} end

FinSet(set::FinSet) = set
