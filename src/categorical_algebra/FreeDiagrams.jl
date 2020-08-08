""" Free diagrams in a category.

A [free diagram](https://ncatlab.org/nlab/show/free+diagram) is a diagram in a
category whose shape is a free category. Examples include the empty diagram,
discrete diagrams, parallel morphisms, spans, and cospans. Limits and colimits
are most commonly taken over free diagrams.
"""
module FreeDiagrams
export Span, Cospan, Diagram, apex, base, left, right,
  DecoratedCospan, AbstractFunctor, AbstractLaxator, LaxMonoidalFunctor,
  decorator, decoration, undecorate

using AutoHashEquals

using ...Theories: dom, codom

# Free diagrams of specific shape
#################################

""" Span of morphisms in a category.
"""
@auto_hash_equals struct Span{Apex,Left,Right}
  apex::Apex
  left::Left
  right::Right
end

function Span(left, right)
  if dom(left) != dom(right)
    error("Domains of legs in span do not match: $left != $right")
  end
  Span(dom(left), left, right)
end

apex(span::Span) = span.apex
left(span::Span) = span.left
right(span::Span) = span.right

""" Cospan of morphisms in a category.
"""
@auto_hash_equals struct Cospan{Base,Left,Right}
  base::Base
  left::Left
  right::Right
end

function Cospan(left, right)
  if codom(left) != codom(right)
    error("Codomains of legs in cospan do not match: $left != $right")
  end
  Cospan(codom(left), left, right)
end

base(cospan::Cospan) = cospan.base
left(cospan::Cospan) = cospan.left
right(cospan::Cospan) = cospan.right

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
