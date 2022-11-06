module LVectors
export LVector

using CompTime

""" Labeled vector.

This is a simplified version of the type `LVector` found in
[LabelledArrays.jl](https://github.com/SciML/LabelledArrays.jl); this version
requires far fewer dependencies. It also has fewer options, but we only need the
functionality implemented here.
"""
struct LVector{Labels,T} <: AbstractVector{T}
  v::Vector{T}
  function LVector{Labels,T}(v::Vector{T}) where {Labels,T}
    @assert length(v) == length(Labels)
    new{Labels,T}(v)
  end
end

LVector{Labels}(v::Vector{T}) where {Labels,T} = LVector{Labels,T}(v)

Base.eltype(::Type{LVector{Labels,T}}) where {Labels,T} = T
Base.copy(v::LVector{Labels,T}) where {Labels,T} = LVector{Labels,T}(copy(v.v))

Base.:(==)(v::LVector{Labels}, v′::LVector{Labels′}) where {Labels,Labels′} =
  Labels == Labels′ && v.v == v′.v
Base.hash(v::LVector{Labels}, h::UInt) where {Labels} =
  hash(Labels, hash(v.v, h))

@inline Base.size(v::LVector) = size(v.v)
@inline Base.length(v::LVector) = length(v.v)

@inline Base.getindex(v::LVector, i::Int) = v.v[i]

@ct_enable function label_to_index(v::LVector{Labels,T}, @ct l) where {Labels,T}
  @ct begin
    i = findfirst(Labels .== l)
    isnothing(i) && error("Label $l not found")
    i
  end
end

@inline Base.getindex(v::LVector, l::Symbol) = v.v[label_to_index(v,Val{l})]

@inline Base.setindex!(v::LVector, x, i::Int) =
  setindex!(v.v, x, i)

@inline Base.setindex!(v::LVector, x, l::Symbol) =
  setindex!(v.v, x, label_to_index(v, Val{l}))

end
