using StructArrays

import Base: length, append!, push!, size

mutable struct StructArrayWithLength{T,N,C,I} <: AbstractArray{T,N}
  sa::StructArray{T,N,C,I}
  n::Int
  function StructArrayWithLength{T}(::Base.UndefInitializer, sz) where {T}
    sa = StructArray{T}(undef,sz)
    _,N,C,I = typeof(sa).parameters
    new{T,N,C,I}(sa,sz)
  end
  function StructArrayWithLength(sa::StructArray{T,N,C,I}) where {T,N,C,I}
    new{T,N,C,I}(sa,length(sa))
  end
  function StructArrayWithLength(v::Vector)
    @assert length(v) >= 1
    sa = StructArray(v)
    T,N,C,I = typeof(sa).parameters
    new{T,N,C,I}(sa,length(v))
  end
  function StructArrayWithLength(n::Int;kw...)
    @assert all(length.(last.([kw...])) .== n)
    sa = StructArray(;kw...)
    T,N,C,I = typeof(sa).parameters
    new{T,N,C,I}(sa,n)
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
Base.@propagate_inbounds Base.getindex(s::StructArrayWithLength, I) = Base.getindex(getfield(s,:sa),I)
