module Mappings
export Mapping, AbstractPartialVector, PartialVector, VecMapStorage, VecMap, DictMap,
  view_with_default

using Reexport

@reexport using ..Defaults

using Base: @propagate_inbounds

# Mappings
##########

"""
A mapping is essentially an AbstractDict, but we support a couple more methods,
like `map`, and so in order to not do type piracy we make our own abstract type
to define methods on. Additionally, access to undefined indices will return
nothing rather than erroring; this means that a Mapping{K,Nothing} will behave
as if everything is undefined. Don't do this.
"""
abstract type Mapping{S,T} <: AbstractDict{S,T} end

# VecMaps
#########

struct VecMap{T, V<:AbstractVector{T}} <: Mapping{Int, T}
  v::V
  defined::BitSet
  function VecMap{T,V}(v::V) where {T,V}
    new{T,V}(v,BitSet(1:length(v)))
  end
  function VecMap{T,V}(v::V, defined::BitSet) where {T,V}
    new{T,V}(v,defined)
  end
end

VecMap{T,V}() where {T,V} = VecMap{T,V}(V())

VecMap{T}() where {T} = VecMap{T,Vector{T}}()

VecMap(v::AbstractVector{T}) where {T} = VecMap{T, typeof(v)}(v)

function VecMap{T,V}(ps...) where {T,V}
  m = VecMap{T,V}()
  for (k,v) in ps
    m[k] = v
  end
  m
end

VecMap{T}(ps...) where {T} = VecMap{T,Vector{T}}(ps...)

function VecMap(p::Pair{Int,T}, ps...) where {T}
  VecMap{T}(p, ps...)
end

function Base.:(==)(m::M, m′::M) where {M<:VecMap}
  for k in keys(m)
    haskey(m′, k) || return false
    m[k] == m′[k] || return false
  end
  for k in keys(m′)
    haskey(m, k) || return false
  end
  return true
end

function extend!(v::AbstractVector, n::Int)
  k = n - length(v)
  Base._growend!(v, k)
end

@propagate_inbounds function _get_or_nothing(m::VecMap, i::Int)
  @boundscheck begin
    if i ∉ m.defined
      return nothing
    end
  end
  @inbounds m.v[i]
end

@propagate_inbounds function Base.getindex(m::VecMap{T}, i::Int) where {T}
  x = _get_or_nothing(m, i)
  if isnothing(x)
    throw(BoundsError(m, i))
  else
    x::T
  end
end

function Base.get(m::VecMap, i::Int, def)
  v = _get_or_nothing(m, i)
  if isnothing(v)
    def
  else
    v
  end
end

function Base.get(f::Any, m::VecMap, i::Int)
  v = _get_or_nothing(m, i)
  if isnothing(v)
    f()
  else
    v
  end
end

@propagate_inbounds function Base.setindex!(m::VecMap, y, i::Int)
  @boundscheck begin
    if i > length(m.v)
      extend!(m.v, i)
    end
  end
  @inbounds m.v[i] = y
  push!(m.defined, i)
end

@propagate_inbounds function Base.setindex!(m::VecMap, ::Nothing, i::Int)
  delete!(m.defined, i)
  m
end

function Base.get!(m::VecMap{T}, i::Int, def::T) where {T}
  v = _get_or_nothing(m, i)
  if isnothing(v)
    m[i] = def
  else
    v
  end
end

function Base.get!(f::Union{Function, Type}, m::VecMap{T}, i::Int) where {T}
  v = _get_or_nothing(m, i)
  if isnothing(v)
    m[i] = f()
  else
    v
  end
end

Base.haskey(m::VecMap, i::Int) = i ∈ m.defined

Base.keys(m::VecMap) = m.defined

Base.copy(m::M) where {M<:VecMap} = M(copy(m.v), copy(m.defined))

Base.delete!(m::VecMap, i) = (delete!(m.defined, i); m)

Base.sizehint!(m::VecMap, n) = sizehint!(m.v, n)

Base.pairs(m::VecMap) = Iterators.map(k -> (k => m[k]), keys(m))

function Base.iterate(m::VecMap)
  iterate(Base.pairs(m))
end

function Base.iterate(m::VecMap, i)
  iterate(Base.pairs(m), i)
end

Base.length(m::VecMap) = foldl((x,_) -> x+1, keys(m); init=0)

struct DictMap{K,V,D<:AbstractDict{K,V}} <: Mapping{K,V}
  d::D
end

DictMap{K,V,D}() where {K,V,D} = DictMap{K,V,D}(D())

DictMap{K,V}() where {K,V} = DictMap{K,V,Dict{K,V}}()

DictMap{K,V,D}(ps...) where {K,V,D} = DictMap{K,V,D}(D(ps...))

DictMap{K,V}(ps...) where {K,V} = DictMap{K,V,Dict{K,V}}(ps...)

DictMap(p::Pair{K,V}, ps...) where {K,V} = DictMap{K,V,Dict{K,V}}(p, ps...)

Base.:(==)(m::M,m′::M) where {M<:DictMap} = m.d == m′.d

Base.getindex(m::DictMap, k) = m.d[k]

Base.get(m::DictMap, k, def) = get(m.d, k, def)

Base.get(f, m::DictMap, k) = get(f, m.d, k)

Base.setindex!(m::DictMap, v, k) = (m.d[k] = v)

Base.setindex!(m::DictMap, ::Nothing, k) = delete!(m.d, k)

Base.get!(m::DictMap, k, def) = get!(m.d, k, def)

Base.get!(f::Union{Function,Type}, m::DictMap, k) = get!(f, m.d, k)

Base.haskey(m::DictMap, k) = haskey(m.d, k)

Base.keys(m::DictMap) = keys(m.d)

Base.copy(m::DictMap) = typeof(m)(copy(m.d))

Base.delete!(m::DictMap, k) = delete!(m.d, k)

Base.pairs(m::DictMap) = pairs(m.d)

Base.iterate(m::DictMap) = iterate(m.d)

Base.iterate(m::DictMap, s) = iterate(m.d, s)

Base.length(m::DictMap) = length(m.d)

Base.sizehint!(m::DictMap, n) = nothing

# Views
#######

struct MappingView{K,V,M<:Mapping{K,V},Def<:Default,Indices<:AbstractVector{K}} <: AbstractVector{V}
  m::M
  indices::Indices
end

@inline _get_default(mv::MappingView{K,V,M,Def}, xs) where {K,V,M,Def} =
  broadcast(xs) do x
    get(() -> default(Def), mv.m, x)
  end

Base.getindex(mv::MappingView, i) = _get_default(mv, mv.indices[i])

Base.values(mv::MappingView) = collect(Iterators.map(i -> _get_default(mv, i), mv.indices))

Base.iterate(mv::MappingView) = iterate(values(mv))

Base.iterate(mv::MappingView, i) = iterate(values(mv), i)

Base.length(mv::MappingView) = length(mv.indices)

Base.size(mv::MappingView) = size(mv.indices)

Base.view(m::Mapping{K,V}, indices) where {K,V} = view_with_default(m, indices, DefaultVal{nothing})

view_with_default(m::Mapping{K,V}, indices, ::Type{Def}) where {K,V,Def<:Default} =
  MappingView{K,V,typeof(m),Def,typeof(indices)}(m, indices)

# Map
#####

function Base.map(f::Function, m::Mapping; out_type=typeof(m))
  m′ = out_type()
  for (k,v) in m
    m′[k] = f(v)
  end
  m′
end

end
