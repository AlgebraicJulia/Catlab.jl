module LVectors
export LVector

using CompTime

"""
This is a simplified version of the LVector found in
[LabelledArrays](https://github.com/SciML/LabelledArrays.jl); this version
requires far fewer dependencies (and fewer options, but we only need the
amount of functionality implemented here).
"""
struct LVector{T,Labels} <: AbstractVector{T}
  v::Vector{T}
  function LVector{T,Labels}(v::Vector{T}) where {T,Labels}
    @assert length(v) == length(Labels)
    new{T,Labels}(v)
  end
end

Base.copy(v::LVector{T,Labels}) where {T,Labels} = LVector{T,Labels}(copy(v.v))
Base.hash(v::LVector, h::UInt) = hash(v.v, h)

@inline Base.getindex(v::LVector, i::Int) = v.v[i]

@ct_enable function label_to_index(v::LVector{T,Labels}, @ct l) where {T,Labels}
  @ct begin
    i = findfirst(Labels .== l)
    if i != nothing
      i
    else
      error("label $l not found")
    end
  end
end

@inline Base.getindex(v::LVector, l::Symbol) = v.v[label_to_index(v,Val{l})]

@inline Base.setindex!(v::LVector{T}, x::T, i::Int) where {T} =
  setindex!(v.v, x, i)

@inline Base.setindex!(v::LVector{T}, x::T, l::Symbol) where {T} =
  setindex!(v.v, x, label_to_index(v, Val{l}))

@inline Base.size(v::LVector) = size(v.v)
@inline Base.length(v::LVector) = length(v.v)

end
