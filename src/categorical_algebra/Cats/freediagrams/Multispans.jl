module Multispans
export Span, Cospan, Multispan, Multicospan, SMultispan, SMulticospan,
        apex, legs, feet, left, right, bundle_legs

using StaticArrays: StaticVector, SVector

using StructEquality
using .....Theories: pair, copair, id, dom, codom
using ..FreeDiagrams
import ..FreeDiagrams: ob, cocone_objects, cone_objects

# Spans and cospans
#------------------

""" Multispan of morphisms in a category.

A [multispan](https://ncatlab.org/nlab/show/multispan) is like a [`Span`](@ref)
except that it may have a number of legs different than two. A colimit of this
shape is a pushout.
"""
@struct_hash_equal struct Multispan{Ob,Hom,Legs<:AbstractVector{Hom}} <:
    FixedShapeFreeDiagram{Ob,Hom}
  apex::Ob
  legs::Legs
end

function Multispan(legs::AbstractVector)
  !isempty(legs) || error("Empty list of legs but no apex given")
  allequal(dom.(legs)) || error("Legs $legs do not have common domain")
  Multispan(dom(first(legs)), legs)
end

const SMultispan{N,Ob,Hom} = Multispan{Ob,Hom,<:StaticVector{N,Hom}}

SMultispan{N}(apex, legs::Vararg{Any,N}) where N =
  Multispan(apex, SVector{N}(legs...))
SMultispan{0}(apex) = Multispan(apex, SVector{0,typeof(id(apex))}())
SMultispan{N}(legs::Vararg{Any,N}) where N = Multispan(SVector{N}(legs...))

""" Span of morphims in a category.

A common special case of [`Multispan`](@ref). See also [`Cospan`](@ref).
"""
const Span{Ob,Hom} = SMultispan{2,Ob,Hom}

""" Apex of multispan or multicospan.

The apex of a multi(co)span is the object that is the (co)domain of all the
[`legs`](@ref).
"""
apex(span::Multispan) = span.apex

""" Legs of multispan or multicospan.

The legs are the morphisms comprising the multi(co)span.
"""
legs(span::Multispan) = span.legs

""" Feet of multispan or multicospan.

The feet of a multispan are the codomains of the [`legs`](@ref).
"""
feet(span::Multispan) = map(codom, span.legs)

""" Left leg of span or cospan.
"""
left(span::Span) = span.legs[1]

""" Right leg of span or cospan.
"""
right(span::Span) = span.legs[2]

cocone_objects(span::Multispan) = feet(span)

Base.iterate(span::Multispan, args...) = iterate(span.legs, args...)
Base.eltype(span::Multispan) = eltype(span.legs)
Base.length(span::Multispan) = length(span.legs)

""" Multicospan of morphisms in a category.

A multicospan is like a [`Cospan`](@ref) except that it may have a number of
legs different than two. A limit of this shape is a pullback.
"""
@struct_hash_equal struct Multicospan{Ob,Hom,Legs<:AbstractVector{Hom}} <:
    FixedShapeFreeDiagram{Ob,Hom}
  apex::Ob
  legs::Legs
end

function Multicospan(legs::AbstractVector)
  !isempty(legs) || error("Empty list of legs but no apex given")
  allequal(codom.(legs)) || error("Legs $legs do not have common codomain")
  Multicospan(codom(first(legs)), legs)
end

const SMulticospan{N,Ob,Hom} = Multicospan{Ob,Hom,<:StaticVector{N,Hom}}

SMulticospan{N}(apex, legs::Vararg{Any,N}) where N =
  Multicospan(apex, SVector{N}(legs...))
SMulticospan{0}(apex) = Multicospan(apex, SVector{0,typeof(id(apex))}())
SMulticospan{N}(legs::Vararg{Any,N}) where N = Multicospan(SVector{N}(legs...))

""" Cospan of morphisms in a category.

A common special case of [`Multicospan`](@ref). See also [`Span`](@ref).
"""
const Cospan{Ob,Hom} = SMulticospan{2,Ob,Hom}

apex(cospan::Multicospan) = cospan.apex
legs(cospan::Multicospan) = cospan.legs
feet(cospan::Multicospan) = map(dom, cospan.legs)
left(cospan::Cospan) = cospan.legs[1]
right(cospan::Cospan) = cospan.legs[2]

cone_objects(cospan::Multicospan) = feet(cospan)

Base.iterate(cospan::Multicospan, args...) = iterate(cospan.legs, args...)
Base.eltype(cospan::Multicospan) = eltype(cospan.legs)
Base.length(cospan::Multicospan) = length(cospan.legs)

""" Bundle together legs of a multi(co)span.

For example, calling `bundle_legs(span, SVector((1,2),(3,4)))` on a multispan
with four legs gives a span whose left leg bundles legs 1 and 2 and whose right
leg bundles legs 3 and 4. Note that in addition to bundling, this function can
also permute legs and discard them.

The bundling is performed using the universal property of (co)products, which
assumes that these (co)limits exist.
"""
bundle_legs(span::Multispan, indices) =
  Multispan(apex(span), map(i -> bundle_leg(span, i), indices))
bundle_legs(cospan::Multicospan, indices) =
  Multicospan(apex(cospan), map(i -> bundle_leg(cospan, i), indices))

bundle_leg(x::Union{Multispan,Multicospan}, i::Int) = legs(x)[i]
bundle_leg(x::Union{Multispan,Multicospan}, i::Tuple) = bundle_leg(x, SVector(i))
bundle_leg(span::Multispan, i::AbstractVector{Int}) = pair(legs(span)[i])
bundle_leg(cospan::Multicospan, i::AbstractVector{Int}) = copair(legs(cospan)[i])

end # module