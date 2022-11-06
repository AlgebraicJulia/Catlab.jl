module ColumnImplementations
export column_type, indexchoice,
  HomChoice, AttrChoice, NoIndex, Index, UniqueIndex, Sparse, Dense

using MLStyle
using StructEquality
using StaticArrays
using ..IndexUtils
using ..Columns


"""
This is a mapping backed by a vector.

The predomain for this mapping is `1:length(v)`, and the defined domain is
`[x for x in 1:length(v) if defined[x]]`. The stored domain is equal to the
defined domain.

As a partial mapping, `getindex` will error outside of the defined domain.
"""
@struct_hash_equal struct PartialVecMap{T, V<:AbstractVector{T}} <: PartialMapping{Int,T}
  v::V
  defined::BitVector
  function PartialVecMap{T,V}(n::Int) where {T, V<:AbstractVector{T}}
    new{T,V}(V(undef, n), falses(n))
  end
  function PartialVecMap{T,V}() where {T, V<:AbstractVector{T}}
    PartialVecMap{T,V}(0)
  end
  function PartialVecMap(v::V, defined::BitVector) where {T, V<:AbstractVector{T}}
    new{T,V}(v, defined)
  end
end

# Check that the defined domains are the same, and then check that the maps are
# equal on their defined domains.
function Base.:(==)(m1::PartialVecMap{T}, m2::PartialVecMap{T}) where {T}
  n = min(length(m1.v), length(m2.v))
  all(.!m1.defined[(n+1):end]) &&
    all(.!m2.defined[(n+1):end]) &&
    all(m1.defined[1:n] .== m2.defined[1:n]) &&
    all((m1.defined[i] && (m1[i] == m2[i])) || !m1.defined[i] for i in 1:n)
end

function Base.getindex(m::PartialVecMap, x::Int)
  @assert m.defined[x]
  m.v[x]
end

function Base.setindex!(m::PartialVecMap, y, x::Int)
  m.defined[x] = true
  m.v[x] = y
end

function Base.view(m::PartialVecMap, xs)
  view(m.v, xs)
end

Base.copy(m::PartialVecMap) = PartialVecMap(copy(m.v), copy(m.defined))

# Assumes that m : T -> T
function Base.map(f, m::PartialVecMap{T}) where {T}
  v′= Vector{T}(undef, length(m.v))
  for i in 1:length(m.v)
    if Columns.isdefined(m, i)
      v′[i] = f(m.v[i])
    end
  end
  PartialVecMap(v′, copy(m.defined))
end

Columns.isdefined(m::PartialVecMap, x::Int) = m.defined[x]

function Columns.undefine_or_clear!(m::PartialVecMap, x::Int)
  m.defined[x] = false
end

Columns.isdefinable(m::PartialVecMap, x::Int) = x ∈ 1:length(m.v)

function Columns.set_definable!(m::PartialVecMap, xs::Base.OneTo{Int})
  n = length(m.v)
  resize!(m.v, xs.stop)
  resize!(m.defined, xs.stop)
  m.defined[(n+1):xs.stop] .= false
end

Columns.isstored(m::PartialVecMap, x) = true

Columns.store!(m::PartialVecMap, x) = nothing

"""
This is a hack in order to pass in a default initializer for
[`DefaultVecMap`](@ref) as a type parameter
"""
abstract type Default{T} end

struct DefaultVal{T,x} <: Default{T}
end

default(::Type{DefaultVal{T,x}}) where {T,x} = x

struct DefaultEmpty{T} <: Default{T}
end

default(::Type{DefaultEmpty{T}}) where {T} = T()

"""
This is the "DefaultMapping" version of `PartialVecMap`. There are two concrete
subtypes of this; one in which we assume that the default value is disjoint from
the valid values (SentinelVecMap), and one in which we assume that the default
value is a valid value (FilledVecMap).
"""
abstract type DefaultVecMap{T, D<:Default{T}} <: DefaultMapping{Int, T} end

function (Ty::DefaultVecMap{T,D})(n::Int) where {T,D}
  Ty([default(D) for i in 1:n])
end
function (Ty::DefaultVecMap{T,D})() where {T,D}
  Ty(T[])
end
function (Ty::DefaultVecMap{T,D})(v::AbstractVector{T}) where {T,D}
  Ty(v)
end

"""
In a SentinelVecMap, the defined indices are the indices for which the value is
not the default; the default is a "sentinel value" marking undefinedness.
"""
@struct_hash_equal struct SentinelVecMap{T,D<:Default{T},V<:AbstractVector{T}} <: DefaultVecMap{T,D}
  v::V
  function SentinelVecMap{T,D,V}() where {T,D,V<:AbstractVector{T}}
    new{T,D,V}(V())
  end
  function SentinelVecMap{T,D,V}(v::V) where {T,D,V<:AbstractVector{T}}
    new{T,D,V}(v)
  end
end

"""
In a FilledVecMap, the defined indices are equal to the definable indices. When
the definable indices are expanded, they are filled with the default value, and
thus the defined indices are also expanded.
"""
@struct_hash_equal struct FilledVecMap{T,D<:Default{T},V<:AbstractVector{T}} <: DefaultVecMap{T,D}
  v::V
  function FilledVecMap{T,D,V}() where {T,D,V}
    new{T,D,V}(V())
  end
  function FilledVecMap{T,D}(v::AbstractVector{T}) where {T,D}
    new{T,D,typeof(v)}(v)
  end
  function FilledVecMap{T,D,V}(v::V) where {T,D,V}
    new{T,D,V}(v)
  end
end

Base.getindex(m::DefaultVecMap, x) = m.v[x]

function Base.setindex!(m::DefaultVecMap, y, x::Int)
  m.v[x] = y
end

function Base.view(m::DefaultVecMap, xs)
  view(m.v, xs)
end


Base.copy(m::M) where {T,D,M<:DefaultVecMap{T,D}} = M(copy(m.v))

# This only works if f::T->T
Base.map(f, m::M) where {T,D,M<:DefaultVecMap{T,D}} = M(map(f, m.v))

Columns.isdefined(m::SentinelVecMap{T,D}, x::Int) where {T,D} = m.v[x] != default(D)

Columns.isdefined(m::FilledVecMap{T,D}, x::Int) where {T,D} = true

Columns.isdefinable(m::DefaultVecMap, x::Int) = x ∈ 1:length(m.v)

function Columns.undefine_or_clear!(m::DefaultVecMap{T,D}, x::Int) where {T,D}
  m.v[x] = default(D)
end

function Columns.set_definable!(m::DefaultVecMap{T,D}, xs::Base.OneTo{Int}) where {T,D}
  n = length(m.v)
  resize!(m.v, xs.stop)
  for i in (n+1):xs.stop
    m.v[i] = default(D)
  end
end

Columns.isstored(m, x) = true
Columns.store!(m, x) = nothing

"""
This is a dictionary-backed mapping, that is partial.
"""
@struct_hash_equal struct PartialDictMap{S,T,D<:AbstractDict{S,T}} <: PartialMapping{S,T}
  d::D
end


PartialDictMap{S,T}(pairs) where {S,T} = PartialDictMap{S,T,Dict{S,T}}(Dict{S,T}(pairs))
PartialDictMap{S,T,D}() where {S,T,D<:AbstractDict{S,T}} = PartialDictMap{S,T,D}(D())

Base.getindex(m::PartialDictMap, xs) =
  broadcast(xs) do x
    m.d[x]
  end

function Base.setindex!(m::PartialDictMap{S}, y, x::S) where {S}
  m.d[x] = y
end

Base.view(m::PartialDictMap, xs) = view(m.d, xs)

Base.copy(m::PartialDictMap{S,T}) where {S,T} = PartialDictMap{S,T}(copy(m.d))

# Note: this only works if f::T->T
Base.map(f, m::PartialDictMap{S,T}) where {S,T} =
  PartialDictMap{S,T}([(k,f(v)) for (k,v) in m.d])

Columns.isdefined(m::PartialDictMap{S}, x::S) where {S} = x ∈ keys(m.d)
Columns.undefine_or_clear!(m::PartialDictMap{S}, x::S) where {S} = delete!(m.d, x)

Columns.isdefinable(m::PartialDictMap{S}, x::S) where {S} = true

Columns.set_definable!(m::PartialDictMap, x) = nothing

Columns.isstored(m::PartialDictMap, x) = true
Columns.store!(m::PartialDictMap, x) = nothing

"""
This is a dictionary-backed mapping that returns a default value
when accessed at an undefined index.
"""
@struct_hash_equal struct DefaultDictMap{S,T,Def<:Default{T},D<:AbstractDict{S,T}} <: DefaultMapping{S,T}
  d::D
end

DefaultDictMap{S,T,Def}(pairs) where {S,T,Def<:Default{T}} =
  DefaultDictMap{S,T,Def,Dict{S,T}}(Dict{S,T}(pairs))

DefaultDictMap{S,T,Def, D}() where {S,T,Def<:Default{T}, D<:AbstractDict{S,T}} =
  DefaultDictMap{S,T,Def,D}(D())

function Base.getindex(m::DefaultDictMap{S,T,Def,D}, x::S) where 
    {S,T,Def<:Default{T},D<:AbstractDict{S,T}}
  if x ∈ keys(m.d)
    m.d[x]
  else
    default(Def)
  end
end

function Base.getindex(m::DefaultDictMap, xs)
  map(xs) do x
    m[x]
  end
end

function Base.setindex!(m::DefaultDictMap, y, x)
  m.d[x] = y
end

Base.copy(m::DefaultDictMap{S,T,D}) where {S,T,D} = DefaultDictMap{S,T,D}(copy(m.d))

Base.map(f, m::DefaultDictMap{S,T,D}) where {S,T,D} =
  DefaultDictMap{S,T,D}([(k,f(v)) for (k,v) in m.d])

Base.view(m::DefaultDictMap, xs) = m[xs]

Columns.isdefined(m::DefaultDictMap{S}, x::S) where {S} = true

Columns.undefine_or_clear!(m::DefaultDictMap{S}, x::S) where {S} = delete!(m.d, x)

Columns.isdefinable(m::DefaultDictMap{S}, x::S) where {S} = true

Columns.set_definable!(::DefaultDictMap, x) = nothing

Columns.isstored(m::DefaultDictMap{S}, x::S) where {S} = x ∈ keys(m.d)

function Columns.store!(m::DefaultDictMap{S,T,Def}, x::S) where {S,T,Def}
  if !(x ∈ keys(m.d))
    m.d[x] = default(Def)
  end
end

"""
The trivial preimage mapping. It just computes preimages on the fly, and the
operations for updating it are noops
"""
struct TrivialCache{S,T} <: PreimageCache{S,T}
end

Base.copy(i::TrivialCache) = i

function Columns.preimage(dom, m::Mapping{S,T}, i::TrivialCache{S,T}, y) where {S,T}
  [x for x in dom if m[x] == y]
end

function Columns.preimage_multi(dom, m::Mapping{S,T}, i::TrivialCache{S,T}, ys) where {S,T}
  map(y -> preimage(dom, m, i, y), ys)
end

Columns.add_mapping!(i::TrivialCache, x, y) = nothing
Columns.remove_mapping!(i::TrivialCache, y, x) = nothing
Columns.set_definable!(i::TrivialCache, ys) = nothing
Columns.store!(i::TrivialCache, y) = nothing
Columns.maybe_unstore!(i::TrivialCache, y) = nothing

"""
An preimage mapping that works by storing the preimages directly. Note: the
storage should be a storage that defaults to making empty preimages when
expanded or queried out of band, so for instance
`DefaultVecMap{Preimage, DefaultEmpty{Preimage}}`
"""
@struct_hash_equal struct StoredPreimageCache{S,T,Preimage<:AbstractSet{S},Storage<:Mapping{T,Preimage}} <: PreimageCache{S,T}
  preimages::Storage
  function StoredPreimageCache(preimages::Storage) where {S,T,Preimage<:AbstractSet{S}, Storage<:Mapping{T,Preimage}}
    new{S,T,Preimage,Storage}(preimages)
  end
  function StoredPreimageCache{S,T,Preimage,Storage}() where {S,T,Preimage<:AbstractSet{S},Storage<:Mapping{T,Preimage}}
    new{S,T,Preimage,Storage}(Storage())
  end
end

Base.copy(i::StoredPreimageCache) = StoredPreimageCache(copy(map(copy, i.preimages)))

function Columns.preimage(dom, m::Mapping{S,T}, i::StoredPreimageCache{S,T}, y) where {S,T}
  values(i.preimages[y])
end

function Columns.preimage_multi(dom, m::Mapping, i::StoredPreimageCache, ys)
  map(values, @view i.preimages[ys])
end

# Assumes that i.preimages[y] is already stored
function Columns.add_mapping!(i::StoredPreimageCache{S,T}, y::T, x::S) where {S,T}
  push!(i.preimages[y], x)
end

function Columns.remove_mapping!(i::StoredPreimageCache{S,T}, y::T, x::S) where {S,T}
  if Columns.isdefined(i.preimages, y)
    delete!(i.preimages[y], x)
  end
end

function Columns.store!(i::StoredPreimageCache{S,T}, y::T) where {S,T}
  store!(i.preimages, y)
end

function Columns.maybe_unstore!(i::StoredPreimageCache{S,T}, y::T) where {S,T}
  if isempty(i.preimages[y])
    undefine_or_clear!(i.preimages, y)
  end
end

function Columns.set_definable!(i::StoredPreimageCache, ys)
  set_definable!(i.preimages, ys)
end

"""
An preimage mapping for injective maps.
"""
@struct_hash_equal struct InjectiveCache{S,T,Storage<:Mapping{T,S}} <: PreimageCache{S,T}
  inverse::Storage
  function InjectiveCache(preimage::Storage) where {S,T,Storage<:Mapping{T,S}}
    new{S,T,Storage}(preimage)
  end
  function InjectiveCache{S,T,Storage}() where {S,T,Storage<:Mapping{T,S}}
    new{S,T,Storage}(Storage())
  end
end

Base.copy(i::InjectiveCache) = InjectiveCache(copy(i.inverse))

function Columns.preimage(dom, m::Mapping{S,T}, i::InjectiveCache{S,T}, y) where {S,T}
  if Columns.isdefined(i.inverse, y)
    SVector{1}(i.inverse[y])
  else
    SVector{0,S}()
  end
end

function Columns.add_mapping!(i::InjectiveCache{S,T}, y::T, x::S) where {S,T}
  if Columns.isdefined(i.inverse, y)
    error("injectivity violated")
  else
    i.inverse[y] = x
  end
end

function Columns.remove_mapping!(i::InjectiveCache{S,T}, y::T, x::S) where {S,T}
  undefine_or_clear!(i.inverse, y)
end


Columns.store!(i::InjectiveCache, y) = nothing
Columns.maybe_unstore!(i::InjectiveCache, y) = nothing

function Columns.set_definable!(i::InjectiveCache, ys)
  set_definable!(i.inverse, ys)
end

# Column types for acsets
#########################

# There are many ways to mix and match mappings and preimage mappings
# Here we present a way of constructing sensible defaults for ACSets
# We make these concrete struct types for ease of debugging
#
# Note: maybe these could be generated with a macro?

"""
A column for a vec-backed unindexed hom
"""
struct DenseFinColumn{V<:AbstractVector{Int}} <: Column{Int,Int}
  m::SentinelVecMap{Int, DefaultVal{Int, 0}, V}
  i::TrivialCache{Int, Int}
end

"""
A column for a vec-backed indexed hom
"""
struct DenseIndexedFinColumn{V<:AbstractVector{Int}} <: Column{Int,Int}
  m::SentinelVecMap{Int, DefaultVal{Int, 0}, V}
  i::StoredPreimageCache{Int, Int, SortedSet{Int},
                      FilledVecMap{SortedSet{Int},
                      DefaultEmpty{SortedSet{Int}},Vector{SortedSet{Int}}}}
end


"""
A column for a vec-backed injective hom
"""
struct DenseInjectiveFinColumn{V<:AbstractVector{Int}} <: Column{Int,Int}
  m::SentinelVecMap{Int, DefaultVal{Int, 0}, V}
  i::InjectiveCache{Int, Int, SentinelVecMap{Int, DefaultVal{Int,0}, Vector{Int}}}
end

# Compatibility hack to support unique_index
function Columns.preimage(dom, c::DenseInjectiveFinColumn, y::Int, ::UnboxInjectiveFlag)
  # @warn "using old convention for preimage of unique-indexed homomorphisms"
  c.i.inverse[y]
end

function Columns.preimage_multi(dom, c::DenseInjectiveFinColumn, ys, ::UnboxInjectiveFlag)
  # @warn "using old convention for preimage of unique-indexed homomorphisms"
  c.i.inverse[ys]
end


"""
A column for a dict-backed unindexed hom with key type K
"""
struct SparseFinColumn{K, D<:AbstractDict{K,K}} <: Column{K,K}
  m::PartialDictMap{K, K, D}
  i::TrivialCache{K, K}
end

"""
A column for a dict-backed indexed hom with key type K
"""
struct SparseIndexedFinColumn{K,D<:AbstractDict{K,K}} <: Column{K,K}
  m::PartialDictMap{K, K, D}
  i::StoredPreimageCache{K, K, Set{K},
                         DefaultDictMap{K, Set{K}, DefaultEmpty{Set{K}},
                                        Dict{K,Set{K}}}}
end

"""
A column for a dict-backed injective hom with key type K
"""
struct SparseInjectiveFinColumn{K} <: Column{K,K}
  m::PartialDictMap{K,K}
  i::InjectiveCache{K,K,PartialDictMap{K,K, Dict{K,K}}}
end

"""
A column for a vec-backed unindexed attr
"""
struct DenseColumn{T, V<:AbstractVector{T}} <: Column{Int,T}
  m::PartialVecMap{T,V}
  i::TrivialCache{Int,T}
end

"""
A column for a vec-backed indexed attr
"""
struct DenseIndexedColumn{T, V<:AbstractVector{T}} <: Column{Int,T}
  m::PartialVecMap{T,V}
  i::StoredPreimageCache{Int, T, SortedSet{Int},
                      DefaultDictMap{T, SortedSet{Int}, 
                      DefaultEmpty{SortedSet{Int}}, Dict{T, SortedSet{Int}}}}
end

"""
A column for a vec-backed unindexed attr
"""
struct DenseInjectiveColumn{T, V<:AbstractVector{T}} <: Column{Int,T}
  m::PartialVecMap{T,V}
  i::InjectiveCache{Int, T, PartialDictMap{T, Int,Dict{T,Int},}}
end

# Compatibility hack
function Columns.preimage(dom, c::DenseInjectiveColumn{T}, y::T, ::UnboxInjectiveFlag) where {T}
  # @warn "using old convention for preimage of unique-indexed attributes"
  get(c.i.inverse.d, y, 0)
end

function Columns.preimage_multi(dom, c::DenseInjectiveColumn, ys, ::UnboxInjectiveFlag)
  # @warn "using old convention for preimage of unique-indexed attributes"
  broadcast(ys) do y
    get(c.i.inverse.d, y, 0)
  end
end

"""
A column for a dict-backed unindexed hom with key type K
"""
struct SparseColumn{K, T} <: Column{K,T}
  m::PartialDictMap{K, T}
  i::TrivialCache{K, T}
end

"""
A column for a dict-backed indexed hom with key type K
"""
struct SparseIndexedColumn{K, T} <: Column{K,T}
  m::PartialDictMap{K, T}
  i::StoredPreimageCache{K, T, Set{K},
                      DefaultDictMap{T, Set{K}, DefaultEmpty{Set{K}}}}
end

"""
A column for a dict-backed injective hom with key type K
"""
struct SparseInjectiveColumn{K, T} <: Column{K,T}
  m::PartialDictMap{K,T}
  i::InjectiveCache{K, T, PartialDictMap{T, K, Dict{K,T}}}
end


@data HomOrAttr begin
  HomChoice
  AttrChoice(T::Any)
end

@data IndexChoice begin
  NoIndex
  Index
  UniqueIndex
end

@data Sparsity begin
  Dense
  Sparse(K::Any)
end

function column_type(hom_or_attr::HomOrAttr, index::IndexChoice, sparsity::Sparsity=Dense)
  @match hom_or_attr begin
    HomChoice => @match sparsity begin
      Dense => @match index begin
        NoIndex => DenseFinColumn{Vector{Int}}
        Index => DenseIndexedFinColumn{Vector{Int}}
        UniqueIndex => DenseInjectiveFinColumn{Vector{Int}}
      end
      Sparse(K) => @match index begin
        NoIndex => SparseFinColumn{K,Dict{K,K}}
        Index => SparseIndexedFinColumn{K,Dict{K,K}}
        UniqueIndex => SparseInjectiveFinColumn{K,Dict{K,K}}
      end
    end
    AttrChoice(T) => @match sparsity begin
      Dense => @match index begin
        NoIndex => DenseColumn{T,Vector{T}}
        Index => DenseIndexedColumn{T,Vector{T}}
        UniqueIndex => DenseInjectiveColumn{T,Vector{T}}
      end
      Sparse(K) => @match index begin
        NoIndex => SparseColumn{K,T,Dict{K,T}}
        Index => SparseIndexedColumn{K,T,Dict{K,T}}
        UniqueIndex => SparseInjectiveColumn{K,T,Dict{K,T}}
      end
    end
  end
end

"""
Convert specification of indexing via lists of indexed and unique_indexed
morphisms into a specific enum choice.
"""
indexchoice(f, index, unique_index) = if f ∈ unique_index
  UniqueIndex
elseif f ∈ index
  Index
else
  NoIndex
end

end
