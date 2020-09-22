""" Structured cospans.

This module provides a generic interface for structured cospans with a concrete
implementation for attributed C-sets.
"""
module StructuredCospans
export StructuredCospan, StructuredMulticospan

using StaticArrays: StaticVector

using ..FreeDiagrams
import ..FreeDiagrams: apex, legs, feet, left, right

""" Structured multicospan.

A structured multicospan is like a structured cospan except that it may have a
number of legs different than two.

See also: [`StructuredCospan`](@ref).
"""
struct StructuredMulticospan{L,X,A,Cosp<:Multicospan{X},Feet<:AbstractVector{A}}
  cospan::Cosp
  feet::Feet
end

""" Structured cospan.

The first type parameter `L` encodes a functor L: A → X from the base category
`A`, often FinSet, to a category `X` with "extra structure." An L-structured
cospan is then a cospan in X whose feet are images under L of objects in A. The
category X is assumed to have pushouts.

Structured cospans form a double category with no assumptions on the functor L.
To obtain a symmetric monoidal double category, L must preserve finite
coproducts. In practice, L usually has a right adjoint R: X → A, which implies
that L preserves all finite colimits. It also allows structured cospans to be
constructed more conveniently from an object x in X plus a cospan in A with apex
R(x).

See also: [`StructuredMulticospan`](@ref).
"""
const StructuredCospan{L,X,A} =
  StructuredMulticospan{L,X,A,<:Cospan{X},<:StaticVector{2,A}}

apex(cospan::StructuredMulticospan) = apex(cospan.cospan)
legs(cospan::StructuredMulticospan) = legs(cospan.cospan)
feet(cospan::StructuredMulticospan) = cospan.feet
left(cospan::StructuredCospan) = first(legs(cospan))
right(cospan::StructuredCospan) = last(legs(cospan))

function StructuredMulticospan{L,X,A}(x::X, cospan::Multicospan{A}) where {L,X,A}
  ϵ = counit(L, x) # Component L(R(x)) → x of counit of adjunction
  StructuredMulticospan{L,X,A}(
    Multicospan(x, map(leg -> L(leg)⋅ϵ, legs(cospan))),
    feet(cospan))
end
StructuredCospan{L,X,A}(apex::X, cospan::Cospan{A}) where {L,X,A} =
  StructuredMulticospan{L,X,A}(apex, cospan)

end
