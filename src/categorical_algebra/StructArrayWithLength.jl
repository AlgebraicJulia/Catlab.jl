using StructArrays

import Base: length, append!, push!, size, copy

const Tup0 = Union{NamedTuple{(),Tuple{}},Tuple{}}

mutable struct StructArrayWithLength{T,C,I} <: AbstractArray{T,1}
  sa::StructArray{T,1,C,I}
  n::Int
  function StructArrayWithLength{T}(::Base.UndefInitializer, sz::Int) where {T}
    sa = StructArray{T}(undef,sz)
    _,_,C,I = typeof(sa).parameters
    new{T,C,I}(sa,sz)
  end
  function StructArrayWithLength(sa::StructArray{T,1,C,I},n::Int) where {T,C,I}
    new{T,C,I}(sa,n)
  end
  function StructArrayWithLength(sa::StructArray{T,1,C,I}) where {T,C,I}
    new{T,C,I}(sa,length(sa))
  end
  function StructArrayWithLength(v::Vector{<:Tup0})
    @assert length(v) >= 1
    sa = StructArray{eltype(v)}(undef, 0)
    T,_,C,I = typeof(sa).parameters
    new{T,C,I}(sa,length(v))
  end
  function StructArrayWithLength(v::Vector)
    @assert length(v) >= 1
    sa = StructArray(v)
    T,_,C,I = typeof(sa).parameters
    new{T,C,I}(sa,length(v))
  end
  function StructArrayWithLength(n::Int;kw...)
    @assert all(length.(last.([kw...])) .== n)
    sa = StructArray(;kw...)
    T,_,C,I = typeof(sa).parameters
    new{T,C,I}(sa,n)
  end
  function StructArrayWithLength(;kw...)
    @assert length([kw...]) != 0
    StructArrayWithLength(length(last([kw...][1]));kw...)
  end
end

length(x::StructArrayWithLength) = getfield(x,:n)

function append!(x::StructArrayWithLength{T},y::StructArrayWithLength{T}) where {T}
  append!(getfield(x,:sa), getfield(y,:sa))
  setfield!(x,:n,length(x)+length(y))
end

function push!(x::StructArrayWithLength{T},y::T) where {T}
  push!(getfield(x,:sa),y)
  setfield!(x,:n,length(x)+1)
end

size(s::StructArrayWithLength) = (length(s),)

Base.getproperty(s::StructArrayWithLength, key::Symbol) = Base.getproperty(getfield(s,:sa),key)
Base.getproperty(s::StructArrayWithLength, key::Int) = Base.getproperty(getfield(s,:sa),key)

Base.getindex(s::StructArrayWithLength{NamedTuple{(),Tuple{}}}, I::Int) = (;)
Base.getindex(s::StructArrayWithLength{Tuple}, I::Int) = ()
Base.getindex(s::StructArrayWithLength, I) = Base.getindex(getfield(s,:sa),I)

Base.setindex!(s::StructArrayWithLength{<:Tup0}, v, I::Int) = nothing
Base.setindex!(s::StructArrayWithLength,v,I::Int) = Base.setindex!(getfield(s,:sa),v,I)

Base.copy(s::StructArrayWithLength) = StructArrayWithLength(copy(getfield(s,:sa)),getfield(s,:n))
