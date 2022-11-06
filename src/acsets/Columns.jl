module Columns
export Mapping, PartialMapping, DefaultMapping,
  isdefined, undefine_or_clear!, isdefinable, set_definable!, isstored, store!,
  PreimageCache, preimage, preimage_multi, add_mapping!, remove_mapping!, maybe_unstore!,
  Column, preimage, preimage_multi, dom_hint!, codom_hint!, undefine!,
  UnboxInjectiveFlag

using MLStyle
using StructEquality
using ..IndexUtils

# Mappings
##########

"""
A `Mapping{S,T}` is a partial, mutable map from type `S` to type `T`.

For a mapping, there are 5 distinct notions of "domain." Mathematically, the
only notions which matter are the domain and the defined domain. But issues of
implementation and performance force us to use domain type definable domain, and
stored domain as well.

1. The type of values in its domain. (Domain type)
2. The subset of values that it can be defined on without erroring. (Definable
   Domain)
3. Its domain. (Domain)
4. The subset of values in its definable domain that it is actually defined on.
   (Defined domain)
5. The subset of defined values that are stored. In general, some of the defined
   values might be dynamically computed; the stored domain is the set of defined
   values where we have actually cached this computation. (Stored domain)

The domain type is a superset of the definable domain, and the definable domain
is a superset of the domain and the defined domain. In general, the defined
domain and the actual domain might have any relation. The defined domain is a
superset of the stored domain.

Additionally, the domain type, definable domain, and defined domain may or may
not be infinite, while the domain and stored domain are always finite.

The mapping knows the domain type, the definable domain, the defined domain, and
the stored domain. It is the responsibility of code outside of the mapping to
keep track of the domain.  This implies that the mapping should be able to be
called without error on any element of its definable domain, because the actual
domain could be any subset of the definable domain.

In general, all 5 of these are distinct notions, but in special cases certain of
these may overlap.

For instance, in a dictionary-based map, the domain type and the definable
domain are equal.  In a map with default values, the defined domain and the
domain are equal. In a vector-backed map, the defined domain and the stored
domain are equal

The mapping keeps track of which elements within its definable domain are
defined, and provides a value in `T` for each element of the defined domain.

Whether or not a value is stored has performance implications for memory use,
but there is also an important semantic distinction. If `i` is stored in a
mapping `i`, then `m[i] === m[i]`.  However, if `i` is defined but not stored,
we have `m[i] == m[i]` but not necessarily `m[i] === m[i]`.  Thus, mutating
`m[i]` will not be saved.

Within this file, elements of `S` will be known as "indices", and elements of
`T` will be known as "values". The sense of "index" as "reverse mapping" will
always be called "preimage", as in [`PreimageCache`](@ref).

`Mapping`s should support the following functions, documented below:
- [`Base.getindex`](@ref)
- [`Base.setindex!`](@ref)
- [`Base.view`](@ref)
- [`Base.copy`](@ref)
- [`Base.map`](@ref)
- [`isdefined`](@ref)
- [`undefine_or_clear!`](@ref)
- [`isdefinable`](@ref)
- [`set_definable!`](@ref)
- [`isstored`](@ref)
- [`store!`](@ref)

In general, for each implementation of Mapping, some of the above functions may
have no effect. This is fine; the intended use of the above functions is to
provide hooks for uses of Mapping to say when performance optimizations can be
taken. It is in fine to ignore these hooks, as long as the semantics of the
mapping are preserved.

The point of the Mapping interface is not for every implementor to have the same
semantics with regard to the functions that manipulate the various domains. The
point is to provide a language in which different implementations can express
their quirks, and for users of Mappings to express options that the
implementations can take advantage of.

Construction
- you should be able to create a mapping from an iterable + a callable 

TODO: come up with a coherent picture for which of these functions are
automatically vectorized.
"""
abstract type Mapping{S,T} end

"""
PartialMappings raise errors when called on elements of their definable domain that are
not in their defined domain.
"""
abstract type PartialMapping{S,T} <: Mapping{S,T} end

"""
A `DefaultMapping` returns a fixed default value when called on an element of
their definable domain that is not in their defined domain.
"""
abstract type DefaultMapping{S,T} <: Mapping{S,T} end

function (::Type{M})(domain, iterable, callable) where {S, T, M <: Mapping{S,T}}
  m = M()
  set_definable!(m, domain)
  for i in iterable
    m[i] = callable(i)
  end
  m
end

function (::Type{M})(domain, callable) where {S, T, M <: Mapping{S,T}}
  M(domain, domain, callable)
end

"""
Arguments:
- m::Mapping{S,T}
- x::S

When called on values outside of the defined domain, the mapping is allowed
to return anything it likes, including an error.

When called on values in its defined domain, the mapping must return the
mathematically correct value.

One should use `isdefined` to determine whether it is safe to call `getindex`.
"""
Base.getindex

"""
Arguments:
- m::Mapping{S,T}
- y::T
- x::S

`x` must be an element of the definable domain; if `x` is not an element of the
definable domain then this function can error or do nothing.

When `x` is an element of the definable domain, `x` is added to the defined domain, and
the value at `x` is set to be `y`.
"""
Base.setindex!


"""
Arguments:
- m::Mapping{S,T}
- xs::Iterable{S}

Semantically, this is the same as mapping Base.getindex over xs, but might be
optionally overridden to return a view of the underlying structure
"""
Base.view

"""
Arguments:
- f::Function
- m::Mapping{S,T}

This should produce a new mapping `m′` with the same domains as `m`, where
`m′[i] = f(m[i])` for all elements `i` of the defined domain of `m`, and where
the type is Mapping{S,T′}, if `f::T->T′`. Note: it is acceptable to only define
this for `f::T->T`.
"""
Base.map

"""
Arguments:
- m::Mapping

This should produce a shallow copy of `m`.
"""
Base.copy

"""
Arguments:
- m::Mapping{S,T}
- x::S

`x` must be an element of the definable domain; returns whether `x` is in the defined
domain.
"""
function isdefined end

"""
Arguments:
- m::Mapping{S,T}
- x::S

Returns whether `x` is in the definable domain of `m`.
"""
function isdefinable end

"""
Arguments:
- m::Mapping{S,T}
- xs::Iterable{S}

Sets the definable domain of the mapping. Typically, `xs` might be `Base.OneTo{Int}`, for
vector-backed mappings.
"""
function set_definable! end

"""
Arguments:
- m::Mapping{S,T}
- x::S

This either removes an index from the defined domain, or sets the value at that
index to the default value. This does not change whether the index is stored.
"""
function undefine_or_clear! end

"""
Arguments:
- m::Mapping{S,T}
- x::S

Returns whether a defined index `x` is stored.
"""
function isstored end

"""
Arguments:
- m::Mapping{S,T}
- x::S

May add an index `x` in the defined domain to the stored domain.
"""
function store! end

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
- [`add_mapping!`](@ref)
- [`remove_mapping!`](@ref)
- [`store!`](@ref)
- [`maybe_unstore!`](@ref)
- [`set_definable!`](@ref)
"""
abstract type PreimageCache{S,T} end

function (::Type{PC})(mapping::Mapping{S,T}, dom, codom) where {S,T,PC<:PreimageCache{S,T}}
  pc = PC()
  set_definable!(pc, codom)
  for i in dom
    add_mapping!(pc, mapping[i], i)
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

Add `x` to the preimage of `y`. If `y` is not in the definable codomain of `i`, this MAY
add `y` to the definable codomain, or MAY error.
"""
function add_mapping! end

"""
Arguments:
- i::PreimageCache{S,T}
- y::T
- x::S

Remove `x` from the preimage of `y`. Assumes that `y` is in the definable codomain of `i`.
"""
function remove_mapping! end

"""
Arguments:
- i::PreimageCache{S,T}
- y::T

Stores the preimage for `y`
"""
# function store! end

"""
Arguments:
- i::PreimageCache{S,T}
- y::T

Might unstore the preimage for `y` if the preimage is empty.
"""
function maybe_unstore! end

"""
Arguments:
- i::PreimageCache{S,T}
- ys::Iterable{T}

Sets the definable codomain of `i`
"""
# set_definable!

# Columns
#########

"""
A column wraps a mapping and a cache of its preimages, and provides methods that
do coordinated updates of both.

Abstract Fields:
- m::Mapping{S,T}
- i::PreimageCache{S,T}
"""
abstract type Column{S,T} end

function (::Type{Col})() where {S,T,Col <: Column{S,T}}
  M, PC = Col.types
  Col(M(), PC())
end

function (::Type{Col})(dom, definable_dom, codom, callable) where {S,T,Col<:Column{S,T}}
  M, PC = Col.types
  m = M(definable_dom, dom, callable)
  pc = PC(m, dom, codom)
  Col(m,pc)
end

function (::Type{Col})(dom, codom, callable) where {S,T,Col<:Column{S,T}}
  Col(dom,dom,codom,callable)
end

Base.:(==)(c1::Column, c2::Column) = c1.m == c2.m

Base.hash(c::Column, h::UInt) = hash(c.m, h)

Base.copy(c::T) where {T <: Column} = T(copy(c.m), copy(c.i))

Base.view(c::Column, xs) = view(c.m, xs)

Base.getindex(c::Column, x) = c.m[x]

function Base.setindex!(c::Column, y, x)
  if isdefined(c.m, x)
    remove_mapping!(c.i, c.m[x], x)
    maybe_unstore!(c.i, c.m[x])
  end
  store!(c.i, y)
  add_mapping!(c.i, y, x)
  c.m[x] = y
end

# This is to maintain compatibility with old convention for unique_indexing
struct UnboxInjectiveFlag end

# This is overloaded for specific columns to enable the old convention
preimage(dom, c::Column, y, ::UnboxInjectiveFlag) = preimage(dom, c, y)

preimage_multi(dom, c::Column, ys, ::UnboxInjectiveFlag) = preimage_multi(dom, c, ys)

preimage(dom, c::Column, y) = preimage(dom, c.m, c.i, y)

preimage_multi(dom, c::Column, ys) = preimage_multi(dom, c.m, c.i, ys)

function undefine!(c::Column{S}, x::S) where {S}
  if isdefined(c.m, x)
    remove_mapping!(c.i, c.m[x], x)
    maybe_unstore!(c.i, c.m[x])
    undefine_or_clear!(c.m, x)
  end
end

function isdefined(c::Column{S}, x::S) where {S}
  isdefined(c.m, x)
end

function dom_hint!(c::Column, xs)
  set_definable!(c.m, xs)
end

function codom_hint!(c::Column, ys)
  set_definable!(c.i, ys)
end

end
