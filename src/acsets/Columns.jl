module Columns
export Mapping, PreimageCache, preimage, preimage_multi, add_mapping!, remove_mapping!,
  Column, preimage, preimage_multi, undefine!,
  UnboxInjectiveFlag

using MLStyle
using StructEquality
using Reexport

@reexport using ..Mappings
@reexport using ..PreimageCaches

import ..Mappings: view_with_default
import ..PreimageCaches: preimage, preimage_multi

# Columns
#########

"""
A column wraps a mapping and a cache of its preimages, and provides methods that
do coordinated updates of both.

Abstract Fields:
- m::Mapping{S,T}
- pc::PreimageCache{S,T}
"""
abstract type Column{S,T} end

function (::Type{Col})() where {Col <: Column}
  M, PC = Col.types
  Col(M(),PC())
end

function (::Type{Col})(pairs...) where {Col<:Column}
  M, PC = Col.types
  m = M(pairs...)
  pc = PC(m)
  Col(m,pc)
end

Base.:(==)(c1::Column, c2::Column) = c1.m == c2.m

Base.hash(c::Column, h::UInt) = hash(c.m, h)

Base.copy(c::T) where {T <: Column} = T(copy(c.m), copy(c.pc))

Base.getindex(c::Column, x) = c.m[x]

Base.get(c::Column, x, def) = get(c.m, x, def)

function Base.setindex!(c::Column, y, x)
  if haskey(c.m, x)
    unassign!(c.pc, c.m[x], x)
  end
  assign!(c.pc, y, x)
  c.m[x] = y
end

# This is to maintain compatibility with old convention for unique_indexing
struct UnboxInjectiveFlag end

# This is overloaded for specific columns to enable the old convention
preimage(dom, c::Column, y, ::UnboxInjectiveFlag) = preimage(dom, c, y)

preimage_multi(dom, c::Column, ys, ::UnboxInjectiveFlag) = preimage_multi(dom, c, ys)

preimage(dom, c::Column, y) = preimage(dom, c.m, c.pc, y)

preimage_multi(dom, c::Column, ys) = preimage_multi(dom, c.m, c.pc, ys)

function Base.delete!(c::Column{S}, x::S) where {S}
  if haskey(c.m, x)
    unassign!(c.pc, c.m[x], x)
    delete!(c.m, x)
  end
end

function Base.haskey(c::Column{S}, x::S) where {S}
  haskey(c.m, x)
end

# Column Views
##############

struct ColumnView{S,T,C <: Column{S,T},I<:AbstractVector{S},Def} <: AbstractVector{T}
  column::C
  indices::I
  def::Def
end

Base.getindex(cv::ColumnView, xs) = broadcast(xs) do x
  get(cv.column, cv.indices[x], cv.def)
end

Base.getindex(cv::ColumnView, xs::AbstractVector{Bool}) =
  [cv[i] for i in 1:length(cv.indices) if xs[i]]

Base.setindex!(cv::ColumnView, y, x) =
  cv.column[cv.indices[x]] = y

Base.view(c::Column, xs) = ColumnView(c, xs, nothing)
view_with_default(c::Column, xs, def) = ColumnView(c, xs, def)

Base.size(c::ColumnView) = size(c.indices)

end
