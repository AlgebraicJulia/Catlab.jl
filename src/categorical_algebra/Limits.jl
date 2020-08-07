""" Limits and colimits in a category.
"""
module Limits
export Cone, Cocone, apex, base, leg, legs, nlegs, pullback, pushout

using AutoHashEquals

using ...Theories
using ..ShapeDiagrams
import ..ShapeDiagrams: apex, base

# Data types
############

""" Cone of morphisms in a category.
"""
@auto_hash_equals struct Cone{S,T}
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

""" Cocone of morphisms in a category.
"""
@auto_hash_equals struct Cocone{S,T}
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
legs(cocone::Cocone) = cocone.legs
nlegs(cocone::Cocone) = length(cocone.legs)

# Limits
########

""" Pullback of a cospan.

The default implementation computes the pullback from products and equalizers.
"""
function pullback(cospan::Cospan)
  f, g = left(cospan), right(cospan)
  prod = product(dom(f), dom(g))
  π1, π2 = left(prod), right(prod)
  eq = equalizer(π1⋅f, π2⋅g)
  Span(eq⋅π1, eq⋅π2)
end

# Colimits
##########

""" Pushout of a span.

The default implementation computes the pushout from coproducts and
coequalizers.
"""
function pushout(span::Span)
  f, g = left(span), right(span)
  coprod = coproduct(codom(f), codom(g))
  ι1, ι2 = left(coprod), right(coprod)
  coeq = coequalizer(f⋅ι1, g⋅ι2)
  Cospan(ι1⋅coeq, ι2⋅coeq)
end

end
