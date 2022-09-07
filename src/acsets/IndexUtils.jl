module IndexUtils
export insertsorted!, deletesorted!, set_attr_index!, unset_attr_index!, SortedSet
using StructEquality

""" Insert into sorted vector, preserving the sorting.
"""
function insertsorted!(a::AbstractVector, x)
  insert!(a, searchsortedfirst(a, x), x)
end

""" Delete one occurrence of value from sorted vector, if present.

Returns whether an occurence was found and deleted.
"""
function deletesorted!(a::AbstractVector, x)
  i = searchsortedfirst(a, x)
  found = i <= length(a) && a[i] == x
  if found; deleteat!(a, i) end
  found
end

""" Set key and value for acset attribute index.
"""
function set_attr_index!(d::AbstractDict{K,<:AbstractVector{Int}},
                         k::K, v::Int) where K
  insertsorted!(get!(d, k) do; Int[] end, v)
end

""" Unset key and value from acset attribute index, if it is set.
"""
function unset_attr_index!(d::AbstractDict{K,<:AbstractVector{Int}},
                           k::K, v::Int) where K
  if haskey(d, k)
    vs = d[k]
    if deletesorted!(vs, v) && isempty(vs)
      delete!(d, k)
    end
  end
end

@struct_hash_equal struct SortedSet{T} <: AbstractSet{T}
  v::Vector{T}
  function SortedSet{T}() where {T}
    new{T}(Vector{T}())
  end
  # Note: only use this if you are sure v is sorted
  function SortedSet{T}(v::Vector{T}) where {T}
    new{T}(v)
  end
end

Base.copy(s::SortedSet{T}) where {T} = SortedSet{T}(copy(s.v))

Base.iterate(s::SortedSet) = iterate(s.v)

Base.push!(s::SortedSet{T}, x::T) where {T} = insertsorted!(s.v, x)
Base.delete!(s::SortedSet{T}, x::T) where {T} = deletesorted!(s.v, x)
Base.in(s::SortedSet{T}, x::T) where {T} = begin
  i = searchsortedfirst(s.v, x)
  i <= length(a) && a[i] == x
end

Base.values(s::SortedSet) = s.v
Base.length(s::SortedSet) = length(s.v)

end
