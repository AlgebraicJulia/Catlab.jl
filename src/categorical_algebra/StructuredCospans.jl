""" Structured cospans.

This module provides a generic interface for structured cospans with a concrete
implementation for attributed C-sets.
"""
module StructuredCospans
export StructuredMulticospan, StructuredCospan, StructuredCospanOb,
  OpenCSetTypes, OpenACSetTypes

using Compat: only

using AutoHashEquals
using StaticArrays: StaticVector, SVector

using ...GAT, ..FreeDiagrams, ..Limits, ..FinSets, ..CSets, ..CSetMorphisms
import ..FreeDiagrams: apex, legs, feet, left, right
using ...Theories: Category, CatDesc, AttrDesc
import ...Theories: dom, codom, compose, ⋅, id

# Generic structured cospans
############################

""" Structured multicospan.

A structured multicospan is like a structured cospan except that it may have a
number of legs different than two.

See also: [`StructuredCospan`](@ref).
"""
@auto_hash_equals struct StructuredMulticospan{L, Cosp <: Multicospan,
                                               Feet <: AbstractVector}
  cospan::Cosp
  feet::Feet

  """ Construct structured multicospan in L-form.
  """
  StructuredMulticospan{L}(cospan::Cosp, feet::Feet) where
      {L, Cosp <: Multicospan, Feet <: AbstractVector} =
    new{L,Cosp,Feet}(cospan, feet)
end

""" Construct structured multicospan in R-form.
"""
function StructuredMulticospan{L}(x, cospan::Multicospan) where L
  StructuredMulticospan{L}(
    Multicospan(x, map(leg -> shift_left(L, x, leg), legs(cospan))),
    feet(cospan))
end

apex(cospan::StructuredMulticospan) = apex(cospan.cospan)
legs(cospan::StructuredMulticospan) = legs(cospan.cospan)
feet(cospan::StructuredMulticospan) = cospan.feet

""" Structured cospan.

The first type parameter `L` encodes a functor L: A → X from the base category
`A`, often FinSet, to a category `X` with "extra structure." An L-structured
cospan is then a cospan in X whose feet are images under L of objects in A. The
category X is assumed to have pushouts.

Structured cospans form a double category with no further assumptions on the
functor L. To obtain a symmetric monoidal double category, L must preserve
finite coproducts. In practice, L usually has a right adjoint R: X → A, which
implies that L preserves all finite colimits. It also allows structured cospans
to be constructed more conveniently from an object x in X plus a cospan in A
with apex R(x).

See also: [`StructuredMulticospan`](@ref).
"""
const StructuredCospan{L, Cosp <: Cospan, Feet <: StaticVector{2}} =
  StructuredMulticospan{L,Cosp,Feet}

""" Construct structured cospan in L-form.
"""
StructuredCospan{L}(cospan::Cospan, feet::StaticVector{2}) where L =
  StructuredMulticospan{L}(cospan, feet)

""" Construct structured cospan in R-form.
"""
StructuredCospan{L}(apex, cospan::Cospan) where L =
  StructuredMulticospan{L}(apex, cospan)

left(cospan::StructuredCospan) = first(legs(cospan))
right(cospan::StructuredCospan) = last(legs(cospan))

# Category of structured cospans
################################

""" Object in the category of L-structured cospans.
"""
@auto_hash_equals struct StructuredCospanOb{L,T}
  ob::T
  StructuredCospanOb{L}(ob::T) where {L,T} = new{L,T}(ob)
end

function StructuredCospan(cospan::Cospan, lfoot::StructuredCospanOb{L},
                          rfoot::StructuredCospanOb{L}) where L
  StructuredCospan{L}(cospan, SVector(lfoot.ob, rfoot.ob))
end

@instance Category{StructuredCospanOb, StructuredCospan} begin
  @import dom, codom, id

  function compose(M::StructuredCospan, N::StructuredCospan)
    ι1, ι2 = colim = pushout(right(M), left(N))
    cospan = Cospan(ob(colim), left(M)⋅ι1, right(N)⋅ι2)
    StructuredCospan(cospan, dom(M), codom(N))
  end
end

dom(cospan::StructuredCospan{L}) where L =
  StructuredCospanOb{L}(first(feet(cospan)))
codom(cospan::StructuredCospan{L}) where L =
  StructuredCospanOb{L}(last(feet(cospan)))

function id(a::StructuredCospanOb{L}) where L
  leg = L(id(a.ob))
  StructuredCospan(Cospan(leg, leg), a, a)
end

# Structured cospans of C-sets
##############################

""" Create types for open C-sets from a C-set type.

Returns two types, for objects, a subtype of [`StructuredCospanOb`](@ref), and
for morphisms, a subtype of [`StructuredCospan`](@ref).

See also: [`OpenACSetTypes`](@ref).
"""
function OpenCSetTypes(::Type{X}, ob₀::Symbol) where
    {CD<:CatDesc, X<:AbstractCSet{CD}}
  @assert ob₀ ∈ CD.ob
  L = FinSetDiscreteACSet{ob₀, X}
  (StructuredCospanOb{L}, StructuredCospan{L})
end

""" Create types for open attributed C-sets from an attributed C-set type.

The resulting types, for objects and morphisms, each have the same type
parameters for data types as the original type.

See also: [`OpenCSetTypes`](@ref).
"""
function OpenACSetTypes(::Type{X}, ob₀::Symbol) where
    {CD<:CatDesc, AD<:AttrDesc{CD}, X<:AbstractACSet{CD,AD}}
  @assert ob₀ ∈ CD.ob
  type_vars = map(TypeVar, AD.data)
  attrs₀ = [ i for (i,j) in enumerate(AD.adom) if CD.ob[j] == ob₀ ]
  L = if isempty(attrs₀)
    FinSetDiscreteACSet{ob₀, X{type_vars...}}
  else
    adom = Tuple(ones(Int, length(attrs₀)))
    CD₀ = CatDesc{(ob₀,),(),(),()}
    AD₀ = AttrDesc{CD₀,AD.data,AD.attr[attrs₀],adom,AD.acodom[attrs₀]}
    DiscreteACSet{ACSet{CD₀,AD₀,Tuple{type_vars...},(),()}, X{type_vars...}}
  end
  (foldr(UnionAll, type_vars, init=StructuredCospanOb{L}),
   foldr(UnionAll, type_vars, init=StructuredCospan{L}))
end

abstract type AbstractDiscreteACSet{X <: AbstractACSet} end

StructuredCospan{L}(x::AbstractACSet, f::FinFunction{Int},
                    g::FinFunction{Int}) where {L<:AbstractDiscreteACSet} =
 StructuredCospan{L}(x, Cospan(f, g))

""" A functor L: FinSet → C-Set giving the discrete C-set wrt an object in C.

This functor has a right adjoint R: C-Set → FinSet giving the underlying set at
that object. Instead of instantiating this type directly, you should use
[`OpenCSetTypes`](@ref) or [`OpenACSetTypes`](@ref).
"""
struct FinSetDiscreteACSet{ob₀, X} <: AbstractDiscreteACSet{X} end

""" A functor L: C₀-Set → C-Set giving the discrete C-set for C₀.

Here C₀ is assumed to contain a single object from C and the discreteness is
with respect to this object. The functor L has a right adjoint R: C-Set → C₀-Set
forgetting the rest of C. Data attributes of the chosen object are preserved.
"""
struct DiscreteACSet{A <: AbstractACSet, X} <: AbstractDiscreteACSet{X} end

function StructuredCospan{L}(
    x::AbstractACSet, cospan::Cospan{<:FinSet{Int}}) where
    {A, L<:DiscreteACSet{A}}
  a = A()
  copy_common_parts!(a, x)
  f, g = cospan
  ϕ, ψ = induced_transformation(a, f), induced_transformation(a, g)
  StructuredCospan{L}(x, Cospan(a, ϕ, ψ))
end

""" C-set transformation b → a induced by function `f` into parts of `a`.
"""
function induced_transformation(a::A, f::FinFunction{Int}) where
    {CD, AD, A <: AbstractACSet{CD,AD}}
  ob = only(CD.ob)
  @assert nparts(a, ob) == length(codom(f))
  b = A()
  add_parts!(b, ob, length(dom(f)))
  f_vec = collect(f)
  for attr in AD.attr
    set_subpart!(b, attr, subpart(a, f_vec, attr))
  end
  ACSetTransformation((; ob => f), b, a)
end

""" Apply left adjoint L: FinSet → C-Set to object.
"""
function (::Type{L})(a::FinSet{Int}) where {ob₀,X,L<:FinSetDiscreteACSet{ob₀,X}}
  x = X()
  add_parts!(x, ob₀, length(a))
  x
end

""" Apply left adjoint L: C₀-Set → C-Set to object.
"""
function (::Type{L})(a::AbstractACSet) where {A,X,L<:DiscreteACSet{A,X}}
  x = X()
  copy_common_parts!(x, a)
  x
end

""" Apply left adjoint L: FinSet → C-Set to morphism.
"""
function (::Type{L})(f::FinFunction{Int}) where
    {ob₀, L <: FinSetDiscreteACSet{ob₀}}
  ACSetTransformation((; ob₀ => f), L(dom(f)), L(codom(f)))
end

""" Apply left adjoint L: C₀-Set → C-Set to morphism.
"""
function (::Type{L})(ϕ::ACSetTransformation) where {L <: DiscreteACSet}
  ACSetTransformation(components(ϕ), L(dom(ϕ)), L(codom(ϕ)))
end

""" Convert morphism a → R(x) to morphism L(a) → x using discrete-forgetful
adjunction L ⊣ R: A ↔ X.
"""
function shift_left(::Type{L}, x::AbstractACSet, f::FinFunction{Int}) where
    {ob₀, L <: FinSetDiscreteACSet{ob₀}}
  ACSetTransformation((; ob₀ => f), L(dom(f)), x)
end
function shift_left(::Type{L}, x::AbstractACSet, ϕ::ACSetTransformation) where
    {L <: DiscreteACSet}
  ACSetTransformation(components(ϕ), L(dom(ϕ)), x)
end

""" Copy parts into a C-set from a C′-set along intersection of C and C′.

TODO: Both more and less general than `copy_parts!` in the `CSets` module: more
general in allowing C != C′, but less general in not copying subparts, only
common data attributes. Ideally this functionality would be unified.
"""
@generated function copy_common_parts!(to::ACSet{CD,AD}, from::ACSet{CD′,AD′}) where
    {CD, AD, CD′, AD′}
  obs = intersect(CD.ob, CD′.ob)
  attrs = intersect(AD.attr, AD′.attr)
  @assert all(dom(AD, attr) == dom(AD′, attr) for attr in attrs)
  Expr(:block,
    :(newparts = (; $(map(obs) do ob
        Expr(:kw, ob, :(add_parts!(to, $(QuoteNode(ob)),
                                   nparts(from, $(QuoteNode(ob))))))
        end...))),
    map(attrs) do attr
      :(set_subpart!(to, newparts.$(dom(AD, attr)), $(QuoteNode(attr)),
                     subpart(from, $(QuoteNode(attr)))))
    end...)
end

end
