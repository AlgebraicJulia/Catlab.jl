""" Diagrams of a given shape.
"""
module ShapeDiagrams
export AbstractFunctor, AbstractLaxator, LaxMonoidalFunctor,
  Span, Cone, Cospan, DecoratedCospan, Cocone, Diagram, left, right, leg, nlegs, apex, base,
  decorator, decoration, undecorate

using ...Theories: dom, codom

abstract type AbstractFunctor end
abstract type AbstractLaxator end

struct LaxMonoidalFunctor{Ftr <: AbstractFunctor, Lxr <: AbstractLaxator} <: AbstractFunctor
  F::Ftr
  L::Lxr
end

""" Span of morphisms in a category.
"""
struct Span{Left,Right}
  left::Left
  right::Right

  function Span(left::Left, right::Right; strict::Bool=true) where {Left,Right}
    if strict && dom(left) != dom(right)
      error("Domains of legs in span do not match: $left vs $right")
    end
    new{Left,Right}(left, right)
  end
end

apex(span::Span) = dom(span.left) # == dom(span.right)
left(span::Span) = span.left
right(span::Span) = span.right

""" Cone of morphisms in a category.
"""
struct Cone{S,T}
  apex::S # We store this separately because legs might be empty
  legs::Vector{T}

  function Cone(apex::S,legs::Vector{T}, strict::Bool=true) where {S,T}
    if strict && !all(dom(leg) == apex for leg in legs)
      error("Domain of legs in cone do not match")
    end
    new{S,T}(apex,legs)
  end
end

apex(cone::Cone) = cone.apex
leg(cone::Cone,n) = cone.legs[n]
legs(cone::Cone) = cone.legs
nlegs(cone::Cone) = length(cone.legs)

""" Cospan of morphisms in a category.
"""
struct Cospan{Left,Right}
  left::Left
  right::Right

  function Cospan(left::Left, right::Right; strict::Bool=true) where {Left,Right}
    if strict && codom(left) != codom(right)
      error("Codomains of legs in cospan do not match: $left vs $right")
    end
    new{Left,Right}(left, right)
  end
end

base(cospan::Cospan) = codom(cospan.left) # == codom(cospan.right)
left(cospan::Cospan) = cospan.left
right(cospan::Cospan) = cospan.right


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

""" Cocone of morphisms in a category.
"""
struct Cocone{S,T}
  base::S # We store this separately because legs might be empty
  legs::Vector{T}

  function Cocone(base::S,legs::Vector{T}, strict::Bool=true) where {S,T}
    if strict && !all(codom(leg) == base for leg in legs)
      error("Codomain of legs in cocone do not match")
    end
    new{S,T}(base,legs)
  end
end

base(cocone::Cocone) = cocone.base
leg(cocone::Cocone,n) = cocone.legs[n]
nlegs(cocone::Cocone) = length(cocone.legs)

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
