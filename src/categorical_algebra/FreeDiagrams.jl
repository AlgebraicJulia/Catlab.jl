""" Free diagrams in a category.

A [free diagram](https://ncatlab.org/nlab/show/free+diagram) in a category is a
diagram whose shape is a free category. Examples include the empty diagram,
discrete diagrams, parallel morphisms, spans, and cospans. Limits and colimits
are most commonly taken over free diagrams.
"""
module FreeDiagrams
export FreeDiagram, FixedFreeDiagram, Span, Cospan, ParallelPair,
  ob, hom, dom, codom, apex, base, legs, nlegs, left, right,
  nv, ne, src, tgt, vertices, edges, has_vertex, has_edge,
  add_vertex!, add_vertices!, add_edge!, add_edges!,
  DecoratedCospan, AbstractFunctor, AbstractLaxator, LaxMonoidalFunctor,
  decorator, decoration, undecorate

import Base: first, last
using AutoHashEquals

import ...Theories: ob, hom, dom, codom
using ...Present, ..CSets, ..Graphs
using ..Graphs: TheoryGraph

# Diagrams of fixed shape
#########################

""" Abstract type for free diagram of fixed shape.
"""
abstract type FixedFreeDiagram{Ob,Hom} end

""" Span of morphisms in a category.

A colimit of this shape is a pushout.
"""
@auto_hash_equals struct Span{Ob,Hom} <: FixedFreeDiagram{Ob,Hom}
  apex::Ob
  left::Hom
  right::Hom

  Span(apex::Ob, left::Left, right::Right) where {Ob,Left,Right} =
    new{Ob,typejoin(Left,Right)}(apex, left, right)
end

function Span(left, right)
  dom(left) == dom(right) ||
    error("Domains of legs in span do not match: $left vs $right")
  Span(dom(left), left, right)
end

apex(span::Span) = span.apex
left(span::Span) = span.left
right(span::Span) = span.right
legs(span::Span) = (left(span), right(span))
nlegs(::Span) = 2

""" Cospan of morphisms in a category.

A limit of this shape is a pullback.
"""
@auto_hash_equals struct Cospan{Ob,Hom} <: FixedFreeDiagram{Ob,Hom}
  base::Ob
  left::Hom
  right::Hom

  Cospan(base::Ob, left::Left, right::Right) where {Ob,Left,Right} =
    new{Ob,typejoin(Left,Right)}(base, left, right)
end

function Cospan(left, right)
  codom(left) == codom(right) ||
    error("Codomains of legs in cospan do not match: $left vs $right")
  Cospan(codom(left), left, right)
end

base(cospan::Cospan) = cospan.base
left(cospan::Cospan) = cospan.left
right(cospan::Cospan) = cospan.right
legs(cospan::Cospan) = (left(cospan), right(cospan))
nlegs(::Cospan) = 2

""" Parallel pair of morphims in a category.

A (co)limit of this shape is a (co)equalizer.
"""
@auto_hash_equals struct ParallelPair{Ob,Hom} <: FixedFreeDiagram{Ob,Hom}
  dom::Ob
  codom::Ob
  first::Hom
  last::Hom

  ParallelPair(dom::Dom, codom::Codom, first::First, last::Last) where
      {Dom,Codom,First,Last} =
    new{typejoin(Dom,Codom),typejoin(First,Last)}(dom, codom, first, last)
end

function ParallelPair(first, last)
  dom(first) == dom(last) ||
    error("Domains of parallel morphisms do not match: $first vs $last")
  codom(first) == codom(last) ||
    error("Codomains of parallel morphisms do not match: $first vs $last")
  ParallelPair(dom(first), codom(first), first, last)
end

dom(pair::ParallelPair) = pair.dom
codom(pair::ParallelPair) = pair.codom
first(pair::ParallelPair) = pair.first
last(pair::ParallelPair) = pair.last

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

function FreeDiagram(span::Span{Ob,Hom}) where {Ob,Hom}
  d = FreeDiagram(ob=Ob, hom=Hom)
  v0 = add_vertex!(d, ob=apex(span))
  vs = add_vertices!(d, nlegs(span), ob=codom.(legs(span)))
  add_edges!(d, repeat([v0], nlegs(span)), vs, hom=legs(span))
  return d
end

function FreeDiagram(cospan::Cospan{Ob,Hom}) where {Ob,Hom}
  d = FreeDiagram(ob=Ob, hom=Hom)
  vs = add_vertices!(d, nlegs(cospan), ob=dom.(legs(cospan)))
  v0 = add_vertex!(d, ob=base(cospan))
  add_edges!(d, vs, repeat([v0], nlegs(cospan)), hom=legs(cospan))
  return d
end

function FreeDiagram(pair::ParallelPair{Ob,Hom}) where {Ob,Hom}
  d = FreeDiagram(ob=Ob, hom=Hom)
  add_vertices!(d, 2, ob=[dom(pair), codom(pair)])
  add_edges!(d, [1,1], [2,2], hom=[first(pair), last(pair)])
  return d
end

end
