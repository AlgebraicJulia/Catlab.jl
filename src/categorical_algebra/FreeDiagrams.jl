""" Free diagrams in a category.

A [free diagram](https://ncatlab.org/nlab/show/free+diagram) in a category is a
diagram whose shape is a free category. Examples include the empty diagram,
pairs of objects, discrete diagrams, parallel morphisms, spans, and cospans.
Limits and colimits are most commonly taken over free diagrams.
"""
module FreeDiagrams
export AbstractFreeDiagram, FreeDiagram, FixedShapeFreeDiagram, DiscreteDiagram,
  EmptyDiagram, ObjectPair, Span, Cospan, Multispan, Multicospan,
  SMultispan, SMulticospan, ParallelPair, ParallelMorphisms,
  ob, hom, dom, codom, apex, legs, feet, left, right, bundle_legs,
  nv, ne, src, tgt, vertices, edges, has_vertex, has_edge,
  add_vertex!, add_vertices!, add_edge!, add_edges!,
  SquareDiagram, top, bottom

using AutoHashEquals
using StaticArrays: StaticVector, SVector, @SVector

using ...Present, ...Theories, ...CSetDataStructures, ...Graphs
import ...Theories: ob, hom, dom, codom, top, bottom, left, right
using ...Graphs.BasicGraphs: TheoryGraph

# Diagrams of fixed shape
#########################

""" Abstract type for free diagram of fixed shape.
"""
abstract type FixedShapeFreeDiagram{Ob} end

# Discrete diagrams
#------------------

""" Discrete diagram: a diagram whose only morphisms are identities.
"""
@auto_hash_equals struct DiscreteDiagram{Ob,Objects<:AbstractVector{Ob}} <:
    FixedShapeFreeDiagram{Ob}
  objects::Objects
end

const EmptyDiagram{Ob} = DiscreteDiagram{Ob,<:StaticVector{0}}
const ObjectPair{Ob} = DiscreteDiagram{Ob,<:StaticVector{2}}

EmptyDiagram{Ob}() where Ob = DiscreteDiagram(@SVector Ob[])
ObjectPair(first, second) = DiscreteDiagram(SVector(first, second))

ob(d::DiscreteDiagram) = d.objects

Base.iterate(d::DiscreteDiagram, args...) = iterate(d.objects, args...)
Base.eltype(d::DiscreteDiagram) = eltype(d.objects)
Base.length(d::DiscreteDiagram) = length(d.objects)
Base.getindex(d::DiscreteDiagram, i) = d.objects[i]
Base.firstindex(d::DiscreteDiagram) = firstindex(d.objects)
Base.lastindex(d::DiscreteDiagram) = lastindex(d.objects)

# Spans and cospans
#------------------

""" Multispan of morphisms in a category.

A [multispan](https://ncatlab.org/nlab/show/multispan) is like a [`Span`](@ref)
except that it may have a number of legs different than two. A colimit of this
shape is a pushout.
"""
@auto_hash_equals struct Multispan{Ob,Hom,Legs<:AbstractVector{Hom}} <:
    FixedShapeFreeDiagram{Ob}
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

apex(span::Multispan) = span.apex
legs(span::Multispan) = span.legs
feet(span::Multispan) = map(codom, span.legs)
left(span::Span) = span.legs[1]
right(span::Span) = span.legs[2]

Base.iterate(span::Multispan, args...) = iterate(span.legs, args...)
Base.eltype(span::Multispan) = eltype(span.legs)
Base.length(span::Multispan) = length(span.legs)

""" Multicospan of morphisms in a category.

A multicospan is like a [`Cospan`](@ref) except that it may have a number of
legs different than two. A limit of this shape is a pullback.
"""
@auto_hash_equals struct Multicospan{Ob,Hom,Legs<:AbstractVector{Hom}} <:
    FixedShapeFreeDiagram{Ob}
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

# Parallel morphisms
#-------------------

""" Parallel morphims in a category.

[Parallel morphisms](https://ncatlab.org/nlab/show/parallel+morphisms) are just
morphisms with the same domain and codomain. A (co)limit of this shape is a
(co)equalizer.

For the common special case of two morphisms, see [`ParallelPair`](@ref).
"""
@auto_hash_equals struct ParallelMorphisms{Dom,Codom,Hom,Homs<:AbstractVector{Hom}} <:
    FixedShapeFreeDiagram{Union{Dom,Codom}}
  dom::Dom
  codom::Codom
  homs::Homs
end

function ParallelMorphisms(homs::AbstractVector)
  @assert !isempty(homs) && allequal(dom.(homs)) && allequal(codom.(homs))
  ParallelMorphisms(dom(first(homs)), codom(first(homs)), homs)
end

""" Pair of parallel morphisms in a category.

A common special case of [`ParallelMorphisms`](@ref).
"""
const ParallelPair{Dom,Codom,Hom} =
  ParallelMorphisms{Dom,Codom,Hom,<:StaticVector{2,Hom}}

function ParallelPair(first, last)
  dom(first) == dom(last) ||
    error("Domains of parallel pair do not match: $first vs $last")
  codom(first) == codom(last) ||
    error("Codomains of parallel pair do not match: $first vs $last")
  ParallelMorphisms(dom(first), codom(first), SVector(first, last))
end

dom(para::ParallelMorphisms) = para.dom
codom(para::ParallelMorphisms) = para.codom
hom(para::ParallelMorphisms) = para.homs

Base.iterate(para::ParallelMorphisms, args...) = iterate(para.homs, args...)
Base.eltype(para::ParallelMorphisms) = eltype(para.homs)
Base.length(para::ParallelMorphisms) = length(para.homs)
Base.getindex(para::ParallelMorphisms, i) = para.homs[i]
Base.firstindex(para::ParallelMorphisms) = firstindex(para.homs)
Base.lastindex(para::ParallelMorphisms) = lastindex(para.homs)

allequal(xs::AbstractVector) = isempty(xs) || all(==(xs[1]), xs)

# Commutative squares
#--------------------

# FIXME: Commutative squares are not free diagrams (they commute!) and so do not
# belong in this module.

"""    SquareDiagram(top, bottom, left, right)

creates a square diagram in a category, which forms the 2-cells of the double category Sq(C).
The four 1-cells are given in top, bottom, left, right order, to match the GAT of a double category.
"""
@auto_hash_equals struct SquareDiagram{Ob,Hom,Homs<:AbstractVector{Hom}} <:
    FixedShapeFreeDiagram{Ob}
  corners::Vector{Ob}
  sides::Homs
end

function SquareDiagram(homs::AbstractVector)
  length(homs) == 4 || error("Square diagrams accept exactly 4 homs, in order top, bottom, left, right")
  obs = [dom(homs[1]), dom(homs[2]), dom(homs[4]), codom(homs[4])]

  # checking well-formedness
  # top-left share domains
  @assert dom(homs[1]) == dom(homs[3])
  # bottom-right share codomains
  @assert codom(homs[2]) == codom(homs[4])
  # left-bottom intersection
  @assert codom(homs[3]) == dom(homs[2])
  # top-right intersection
  @assert codom(homs[1]) == dom(homs[4])

  SquareDiagram(obs, homs)
end

SquareDiagram(top, bottom, left, right) = SquareDiagram([top, bottom, left, right])

ob(sq::SquareDiagram) = sq.corners
hom(sq::SquareDiagram) = sq.sides

top(sq::SquareDiagram) = sq.sides[1]
bottom(sq::SquareDiagram) = sq.sides[2]
left(sq::SquareDiagram) = sq.sides[3]
right(sq::SquareDiagram) = sq.sides[4]

# General diagrams
##################

@present TheoryFreeDiagram <: TheoryGraph begin
  Ob::Data
  Hom::Data
  ob::Attr(V,Ob)
  hom::Attr(E,Hom)
end

const FreeDiagram = ACSetType(TheoryFreeDiagram, index=[:src,:tgt])

# XXX: This is needed because we cannot control the supertype of C-set types.
const _AbstractFreeDiagram = AbstractACSetType(TheoryFreeDiagram)
const AbstractFreeDiagram{Ob} =
  Union{_AbstractFreeDiagram{Ob},FixedShapeFreeDiagram{Ob}}

ob(d::FreeDiagram, args...) = subpart(d, args..., :ob)
hom(d::FreeDiagram, args...) = subpart(d, args..., :hom)

function FreeDiagram(obs::AbstractVector{Ob},
                     homs::AbstractVector{Tuple{Hom,Int,Int}}) where {Ob,Hom}
  @assert all(obs[s] == dom(f) && obs[t] == codom(f) for (f,s,t) in homs)
  d = FreeDiagram{Ob,Hom}()
  add_vertices!(d, length(obs), ob=obs)
  add_edges!(d, getindex.(homs,2), getindex.(homs,3), hom=first.(homs))
  return d
end

# Conversion of fixed shapes
#---------------------------

function FreeDiagram(discrete::DiscreteDiagram{Ob}) where Ob
  d = FreeDiagram{Ob,Nothing}()
  add_vertices!(d, length(discrete), ob=collect(discrete))
  return d
end

function FreeDiagram(span::Multispan{Ob,Hom}) where {Ob,Hom}
  d = FreeDiagram{Ob,Hom}()
  v0 = add_vertex!(d, ob=apex(span))
  vs = add_vertices!(d, length(span), ob=feet(span))
  add_edges!(d, fill(v0, length(span)), vs, hom=legs(span))
  return d
end

function FreeDiagram(cospan::Multicospan{Ob,Hom}) where {Ob,Hom}
  d = FreeDiagram{Ob,Hom}()
  vs = add_vertices!(d, length(cospan), ob=feet(cospan))
  v0 = add_vertex!(d, ob=apex(cospan))
  add_edges!(d, vs, fill(v0, length(cospan)), hom=legs(cospan))
  return d
end

function FreeDiagram(para::ParallelMorphisms{Dom,Codom,Hom}) where {Dom,Codom,Hom}
  d = FreeDiagram{Union{Dom,Codom},Hom}()
  add_vertices!(d, 2, ob=[dom(para), codom(para)])
  add_edges!(d, fill(1,length(para)), fill(2,length(para)), hom=hom(para))
  return d
end

function FreeDiagram(sq::SquareDiagram)
    top, bottom, left, right = sq.sides
    # check that the domains and codomains match
    #   1   -top->   3
    #   |            |
    # left         right
    #   v            v
    #   2  -bottom-> 4

    @assert codom(top) == dom(right)
    @assert dom(top) == dom(left)
    @assert dom(bottom) == codom(left)
    @assert codom(bottom) == codom(right)

    V = [dom(left), codom(left), dom(right), codom(right)]
    E = [(top,1,3), (bottom,2,4), (left,1,2), (right,3,4)]
    return FreeDiagram(V, E)
end

end
