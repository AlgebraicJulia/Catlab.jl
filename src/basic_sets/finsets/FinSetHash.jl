module FinSetHash 
export FinSetCollection

using StructEquality

using ..FinSets 
import ..FinSets: FinSet


""" Finite set given by Julia collection.

The underlying collection should be a Julia iterable of definite length. It may
be, but is not required to be, set-like (a subtype of `AbstractSet`).
"""
@struct_hash_equal struct FinSetCollection{S,T} <: FinSet{S,T}
  collection::S
end
FinSetCollection(collection::S) where S =
  FinSetCollection{S,eltype(collection)}(collection)

FinSet(collection::S) where {T, S<:Union{AbstractVector{T},AbstractSet{T}}} =
  FinSetCollection{S,T}(collection)

Base.iterate(set::FinSetCollection, args...) = iterate(set.collection, args...)
Base.length(set::FinSetCollection) = length(set.collection)
Base.in(elem, set::FinSetCollection) = in(elem, set.collection)

function Base.show(io::IO, set::FinSetCollection)
  print(io, "FinSet(")
  show(io, set.collection)
  print(io, ")")
end


end # module
