""" Free diagrams in a category.

A [free diagram](https://ncatlab.org/nlab/show/free+diagram) in a category is a
diagram whose shape is a free category. Examples include the empty diagram,
discrete diagrams, parallel morphisms, spans, and cospans. Limits and colimits
are most commonly taken over free diagrams.
"""
module FreeDiagrams
export FreeDiagram, FixedFreeDiagram,
  Span, Cospan, Multispan, Multicospan, ParallelPair, ParallelMorphisms,
  ob, hom, dom, codom, apex, base, legs, nlegs, left, right,
  nv, ne, src, tgt, vertices, edges, has_vertex, has_edge,
  add_vertex!, add_vertices!, add_edge!, add_edges!,
  DecoratedCospan, AbstractFunctor, AbstractLaxator, LaxMonoidalFunctor,
  decorator, decoration, undecorate

using AutoHashEquals
using StaticArrays: StaticVector, SVector

import ...Theories: ob, hom, dom, codom
using ...Present, ..CSets, ..Graphs
using ..Graphs: TheoryGraph

# Diagrams of fixed shape
#########################

""" Abstract type for free diagram of fixed shape.
"""
abstract type FixedFreeDiagram{Ob,Hom} end

""" Multispan of morphisms in a category.

A [multispan](https://ncatlab.org/nlab/show/multispan) is like a [`Span`](@ref)
except that it may have a number of legs different than two. A colimit of this
shape is a pushout.
"""
@auto_hash_equals struct Multispan{Ob,Hom,Legs<:AbstractVector{Hom}} <:
    FixedFreeDiagram{Ob,Hom}
  apex::Ob
  legs::Legs
end

function Multispan(legs::AbstractVector)
  @assert length(unique(dom.(legs))) == 1
  Multispan(dom(first(legs)), legs)
end

""" Span of morphims in a category.

A common special case of [`Multispan`](@ref). See also [`Cospan`](@ref).
"""
const Span{Ob,Hom} = Multispan{Ob,Hom,<:StaticVector{2,Hom}}

function Span(left, right)
  dom(left) == dom(right) ||
    error("Domains of legs of span do not match: $left vs $right")
  Multispan(dom(left), SVector(left, right))
end

apex(span::Multispan) = span.apex
legs(span::Multispan) = span.legs
nlegs(span::Multispan) = length(span.legs)
left(span::Span) = span.legs[1]
right(span::Span) = span.legs[2]

""" Multicospan of morphisms in a category.

A multicospan is like a [`Cospan`](@ref) except that it may have a number of
legs different than two. A limit of this shape is a pullback.
"""
@auto_hash_equals struct Multicospan{Ob,Hom,Legs<:AbstractVector{Hom}} <:
    FixedFreeDiagram{Ob,Hom}
  base::Ob
  legs::Legs
end

function Multicospan(legs::AbstractVector)
  @assert length(unique(codom.(legs))) == 1
  Multicospan(codom(first(legs)), legs)
end

""" Cospan of morphisms in a category.

A common special case of [`Multicospan`](@ref). See also [`Span`](@ref).
"""
const Cospan{Ob,Hom} = Multicospan{Ob,Hom,<:StaticVector{2,Hom}}

function Cospan(left, right)
  codom(left) == codom(right) ||
    error("Codomains of legs of cospan do not match: $left vs $right")
  Multicospan(codom(left), SVector(left, right))
end

base(cospan::Multicospan) = cospan.base
legs(cospan::Multicospan) = cospan.legs
nlegs(cospan::Multicospan) = length(cospan.legs)
left(cospan::Cospan) = cospan.legs[1]
right(cospan::Cospan) = cospan.legs[2]

""" Parallel morphims in a category.

[Parallel morphisms](https://ncatlab.org/nlab/show/parallel+morphisms) are just
morphisms with the same domain and codomain. A (co)limit of this shape is a
(co)equalizer.

For the common special case of two morphisms, see [`ParallelPair`](@ref).
"""
@auto_hash_equals struct ParallelMorphisms{Ob,Hom,Homs<:AbstractVector{Hom}} <:
    FixedFreeDiagram{Ob,Hom}
  dom::Ob
  codom::Ob
  homs::Homs
end

function ParallelMorphisms(homs::AbstractVector)
  @assert length(unique(dom.(homs))) == 1
  @assert length(unique(codom.(homs))) == 1
  ParallelMorphisms(dom(first(homs)), codom(first(homs)), homs)
end

""" Pair of parallel morphisms in a category.

A common special case of [`ParallelMorphism`](@ref).
"""
const ParallelPair{Ob,Hom} = ParallelMorphisms{Ob,Hom,<:StaticVector{2,Hom}}

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
Base.first(pair::ParallelPair) = pair.homs[1]
Base.last(pair::ParallelPair) = pair.homs[2]

# Decorated cospans
#------------------

# FIXME: Types and structs for functors do not belong here.
abstract type AbstractFunctor end
abstract type AbstractLaxator end

struct LaxMonoidalFunctor{Ftr <: AbstractFunctor, Lxr <: AbstractLaxator} <: AbstractFunctor
  F::Ftr
  L::Lxr
end

""" Decorate Cospan of morphisms for representing open networks.
"""
struct DecoratedCospan{Decorator <: AbstractFunctor,Decoration}
  cospan::Cospan
  decorator::Decorator
  decoration::Decoration
end

decorator(m::DecoratedCospan) = m.decorator
decoration(m::DecoratedCospan) = m.decoration
undecorate(m::DecoratedCospan) = m.cospan
base(m::DecoratedCospan) = base(m.cospan)
left(m::DecoratedCospan) = left(m.cospan)
right(m::DecoratedCospan) = right(m.cospan)

# General diagrams
##################

@present TheoryFreeDiagram <: TheoryGraph begin
  Ob::Ob
  Hom::Ob
  ob::Hom(V,Ob)
  hom::Hom(E,Hom)
end

const FreeDiagram = CSetType(TheoryFreeDiagram, data=[:Ob, :Hom],
                             index=[:src, :tgt])

ob(d::FreeDiagram, args...) = subpart(d, args..., :ob; allowmissing=false)
hom(d::FreeDiagram, args...) = subpart(d, args..., :hom; allowmissing=false)

function FreeDiagram(obs::Vector{Ob},
                     homs::Vector{Tuple{Int,Int,Hom}}) where {Ob,Hom}
  @assert all(obs[s] == dom(f) && obs[t] == codom(f) for (s,t,f) in homs)
  d = FreeDiagram(ob=Ob, hom=Hom)
  add_vertices!(d, length(obs), ob=obs)
  add_edges!(d, getindex.(homs,1), getindex.(homs,2), hom=last.(homs))
  return d
end

# Conversion of fixed shapes
#---------------------------

function FreeDiagram(span::Multispan{Ob,Hom}) where {Ob,Hom}
  d = FreeDiagram(ob=Ob, hom=Hom)
  v0 = add_vertex!(d, ob=apex(span))
  vs = add_vertices!(d, nlegs(span), ob=codom.(legs(span)))
  add_edges!(d, fill(v0, nlegs(span)), vs, hom=legs(span))
  return d
end

function FreeDiagram(cospan::Multicospan{Ob,Hom}) where {Ob,Hom}
  d = FreeDiagram(ob=Ob, hom=Hom)
  vs = add_vertices!(d, nlegs(cospan), ob=dom.(legs(cospan)))
  v0 = add_vertex!(d, ob=base(cospan))
  add_edges!(d, vs, fill(v0, nlegs(cospan)), hom=legs(cospan))
  return d
end

function FreeDiagram(para::ParallelMorphisms{Ob,Hom}) where {Ob,Hom}
  d = FreeDiagram(ob=Ob, hom=Hom)
  add_vertices!(d, 2, ob=[dom(para), codom(para)])
  n = length(hom(para))
  add_edges!(d, fill(1,n), fill(2,n), hom=hom(para))
  return d
end

end
