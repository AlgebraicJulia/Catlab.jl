module PreimageCaches
export PreimageCache, TrivialCache, StoredPreimageCache, InjectiveCache,
  preimage, preimage_multi, assign!, unassign!

using StructEquality
using StaticArrays

using ..Mappings
using ..Defaults
using ..IndexUtils

# Preimage caches
#################

"""
A `PreimageCache` is a cache of the preimage of a `Mapping`. Many of the methods
for `PreimageCache` take in a `Mapping`; this is so that `PreimageCache` can
choose how much to cache. That is, `PreimageCache` could be a unit type, and
simply dynamically compute the preimage mapping on demand, or it could store the
full preimage mapping, or perhaps something in between.

Just like a `Mapping`, an `PreimageCache` has a definable codomain, which is a
subset of `T`. Calling `add_mapping!` and `remove_mapping!` on elements out of
this definable codomain will error.

However, a `PreimageCache` is always defined on all of its definable codomain;
it defaults to the empty set.

`PreimageCache` also has a notion of "stored" codomain, where preimages are
actually stored.  It is only when the preimage is stored that referential
equality of preimage sets will be preserved, and additionally storage can have
performance implications.

`PreimageCache`s should support the following functions:
- [`preimage`](@ref)
- [`assign!`](@ref)
- [`unassign!`](@ref)
"""
abstract type PreimageCache{S,T} end

function (::Type{PC})(mapping::Mapping{S,T}) where {S,T,PC<:PreimageCache{S,T}}
  pc = PC()
  for (k,v) in mapping
    assign!(pc, v, k)
  end
  pc
end

"""
Arguments:
- dom::Iterable{S}
- m::Mapping{S,T}
- i::PreimageCache{S,T}
- y::T

Returns an iterable of the values in the domain that map onto `y`.
"""
function preimage end

"""
Arguments:
- dom::Iterable{S}
- m::Mapping{S,T}
- i::PreimageCache{S,T}
- ys::Iterable{T}

Semantically, this is the same as mapping [`preimage`](@ref) over `ys`, but the
implementation might choose to use a view of an internal data structure of the
index instead.
"""
function preimage_multi(dom, m::Mapping, i::PreimageCache, ys)
  broadcast(ys) do y
    preimage(dom, m, i, y)
  end
end

"""
Arguments:
- i::PreimageCache{S,T}
- y::T
- x::S

Add `x` to the preimage of `y`.
"""
function assign! end

"""
Arguments:
- i::PreimageCache{S,T}
- y::T
- x::S

Remove `x` from the preimage of `y`.
"""
function unassign! end

"""
The trivial preimage mapping. It just computes preimages on the fly, and the
operations for updating it are noops
"""
struct TrivialCache{S,T} <: PreimageCache{S,T}
end

Base.copy(pc::TrivialCache) = pc

function preimage(dom, m::Mapping{S,T}, ::TrivialCache{S,T}, y) where {S,T}
  [x for x in dom if get(m, x, nothing) == y]
end

function preimage_multi(dom, m::Mapping{S,T}, pc::TrivialCache{S,T}, ys) where {S,T}
  map(y -> preimage(dom, m, pc, y), ys)
end

assign!(pc::TrivialCache, x, y) = nothing
unassign!(pc::TrivialCache, y, x) = nothing

"""
An preimage mapping that works by storing the preimages directly. Note: the
storage should be a storage that defaults to making empty preimages when
expanded or queried out of band, so for instance
`DefaultVecMap{Preimage, DefaultEmpty{Preimage}}`
"""
@struct_hash_equal struct StoredPreimageCache{
    S,T,Preimage<:AbstractSet{S},Storage<:Mapping{T,Preimage}} <: PreimageCache{S,T}
  preimages::Storage
  function StoredPreimageCache(preimages::Storage) where
      {S,T,Preimage<:AbstractSet{S}, Storage<:Mapping{T,Preimage}}
    new{S,T,Preimage,Storage}(preimages)
  end
  function StoredPreimageCache{S,T,Preimage,Storage}() where
      {S,T,Preimage<:AbstractSet{S},Storage<:Mapping{T,Preimage}}
    new{S,T,Preimage,Storage}(Storage())
  end
end

Base.copy(pc::StoredPreimageCache) = StoredPreimageCache(copy(map(copy, pc.preimages)))

function preimage(
    dom,
    ::Mapping{S,T},
    pc::StoredPreimageCache{S,T,Preimage},
    y
  ) where {S,T,Preimage}
  values(get(() -> Preimage(), pc.preimages, y))
end

function preimage_multi(dom, m::Mapping, pc::StoredPreimageCache{S,T,Preimage}, ys) where {S,T,Preimage}
  vwd = view_with_default(pc.preimages, ys, DefaultEmpty{Preimage})
  Vector{Vector{S}}(collect(Iterators.map(values, vwd)))
end

# Assumes that i.preimages[y] is already stored
function assign!(pc::StoredPreimageCache{S,T,Preimage}, y::T, x::S) where {S,T,Preimage}
  push!(get!(() -> Preimage(), pc.preimages, y), x)
end

function unassign!(pc::StoredPreimageCache{S,T}, y::T, x::S) where {S,T}
  if haskey(pc.preimages, y)
    delete!(pc.preimages[y], x)
  end
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

Base.copy(pc::InjectiveCache) = InjectiveCache(copy(pc.inverse))

function preimage(dom, ::Mapping{S,T}, pc::InjectiveCache{S,T}, y) where {S,T}
  if haskey(pc.inverse, y)
    SVector{1}(pc.inverse[y])
  else
    SVector{0,S}()
  end
end

function assign!(pc::InjectiveCache{S,T}, y::T, x::S) where {S,T}
  if haskey(pc.inverse, y)
    error("injectivity violated")
  else
    pc.inverse[y] = x
  end
end

function unassign!(pc::InjectiveCache{S,T}, y::T, x::S) where {S,T}
  delete!(pc.inverse, y)
end

end
