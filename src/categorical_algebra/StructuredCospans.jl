""" Structured cospans.

This module provides a generic interface for structured cospans with a concrete
implementation for attributed C-sets.
"""
module StructuredCospans
export StructuredMulticospan, StructuredCospan, StructuredCospanOb,
  OpenCSetTypes, OpenACSetTypes

using AutoHashEquals
using StaticArrays: StaticVector, SVector

using ...GAT, ..FreeDiagrams, ..Limits, ..FinSets, ..CSets, ..CSetMorphisms
import ..FreeDiagrams: apex, legs, feet, left, right
using ...Theories: Category
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

  StructuredMulticospan{L}(cospan::Cosp, feet::Feet) where
      {L, Cosp <: Multicospan, Feet <: AbstractVector} =
    new{L,Cosp,Feet}(cospan, feet)
end

function StructuredMulticospan{L}(apex, cospan::Multicospan) where L
  ϵ = counit(L, apex)
  StructuredMulticospan{L}(
    Multicospan(apex, map(leg -> L(leg)⋅ϵ, legs(cospan))), feet(cospan))
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

StructuredCospan{L}(cospan::Cospan, feet::StaticVector{2}) where L =
  StructuredMulticospan{L}(cospan, feet)
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

function OpenACSetTypes(::Type{X}, ob₀::Symbol) where {CD, X <: AbstractACSet{CD}}
  @assert ob₀ ∈ CD.ob
  L = DiscreteACSet{ob₀,X}
  (StructuredCospanOb{L}, StructuredCospan{L})
end
OpenCSetTypes(::Type{X}, ob₀::Symbol) where {X <: AbstractCSet} =
  OpenACSetTypes(X, ob₀)

struct DiscreteACSet{ob₀, X <: AbstractACSet} end

function (::Type{L})(x₀::FinSet{Int}) where {ob₀, X, L<:DiscreteACSet{ob₀,X}}
  x = X()
  add_parts!(x, ob₀, length(x₀))
  x
end
function (::Type{L})(f₀::FinFunction{Int}) where {ob₀, L<:DiscreteACSet{ob₀}}
  ACSetTransformation((; ob₀ => f₀), L(dom(f₀)), L(codom(f₀)))
end

""" Unit a → R(L(a)) of discrete-forgetful adjunction L ⊣ R: FinSet → C-Set.
"""
unit(::Type{L}, a) where {L<:DiscreteACSet} = id(a)

""" Counit L(R(x)) → x of discrete-forgetful adjunction L ⊣ R: FinSet → CSet.
"""
function counit(::Type{L}, x) where {ob₀, L<:DiscreteACSet{ob₀}}
  x₀ = FinSet(nparts(x, ob₀))
  ACSetTransformation((; ob₀ => id(x₀)), L(x₀), x)
end

end
