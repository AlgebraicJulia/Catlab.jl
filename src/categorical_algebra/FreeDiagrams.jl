""" Free diagrams in a category.

A [free diagram](https://ncatlab.org/nlab/show/free+diagram) is a diagram in a
category whose shape is a free category. Examples include the empty diagram,
discrete diagrams, parallel morphisms, spans, and cospans. Limits and colimits
are most commonly taken over free diagrams.
"""
module FreeDiagrams
export Span, Cospan, ParallelPair, Diagram, dom, codom, apex, base, left, right,
  DecoratedCospan, AbstractFunctor, AbstractLaxator, LaxMonoidalFunctor,
  decorator, decoration, undecorate

using AutoHashEquals

import ...Theories: dom, codom

# Free diagrams of specific shape
#################################

""" Span of morphisms in a category.

A colimit of this shape is a pushout.
"""
@auto_hash_equals struct Span{Apex,Left,Right}
  apex::Apex
  left::Left
  right::Right
end

function Span(left, right)
  dom(left) == dom(right) ||
    error("Domains of legs in span do not match: $left vs $right")
  Span(dom(left), left, right)
end

apex(span::Span) = span.apex
left(span::Span) = span.left
right(span::Span) = span.right

""" Cospan of morphisms in a category.

A limit of this shape is a pullback.
"""
@auto_hash_equals struct Cospan{Base,Left,Right}
  base::Base
  left::Left
  right::Right
end

function Cospan(left, right)
  codom(left) == codom(right) ||
    error("Codomains of legs in cospan do not match: $left vs $right")
  Cospan(codom(left), left, right)
end

base(cospan::Cospan) = cospan.base
left(cospan::Cospan) = cospan.left
right(cospan::Cospan) = cospan.right

""" Parallel pair of morphims in a category.

A (co)limit of this shape is a (co)equalizer.
"""
@auto_hash_equals struct ParallelPair{Dom,Codom,Left,Right}
  dom::Dom
  codom::Codom
  left::Left
  right::Right
end

function ParallelPair(left, right)
  dom(left) == dom(right) ||
    error("Domains of parallel morphisms do not match: $left vs $right")
  codom(left) == codom(right) ||
    error("Codomains of parallel morphisms do not match: $left vs $right")
  Parallel(dom(left), codom(left), left, right)
end

dom(pair::ParallelPair) = pair.dom
codom(pair::ParallelPair) = pair.codom
left(pair::ParallelPair) = pair.left
right(pair::ParallelPair) = pair.right

# Decorated cospans.
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

# General free diagrams
#######################

struct Diagram{Ob,Hom}
  obs::Vector{Ob}
  homs::Vector{Tuple{Int64,Int64,Hom}}

  function Diagram(obs::Vector{Ob}, homs::Vector{Tuple{Int64,Int64,Hom}}) where {Ob, Hom}
    for (s,t,f) in homs
      @assert obs[s] == dom(f)
      @assert obs[t] == codom(f)
    end
    new{Ob,Hom}(obs,homs)
  end
end

end
