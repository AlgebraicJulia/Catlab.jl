export SetOb, TypeSet, PredicatedSet

""" Abstract type for object in the category **Set**.

The type parameter `T` is the element type of the set.

Note: This type is more abstract than the built-in Julia types `AbstractSet` and
`Set`, which are intended for data structures for finite sets. Those are
encompassed by the subtype [`FinSet`](@ref).
"""
abstract type SetOb{T} end
SetOb(S::SetOb) = S
Base.eltype(::Type{<:SetOb{T}}) where T = T
