""" Limits and colimits in a category.
"""
module Limits
export AbstractLimit, AbstractColimit, Limit, Colimit,
  Terminal, BinaryProduct, Product, BinaryPullback, Pullback, Equalizer,
  Initial, BinaryCoproduct, Coproduct, BinaryPushout, Pushout, Coequalizer,
  ob, cone, cocone, apex, base, legs,
  limit, terminal, product, proj1, proj2, equalizer, incl, pullback,
  colimit, initial, coproduct, coproj1, coproj2, coqualizer, proj, pushout

using Compat: only

using AutoHashEquals
using Missings: nonmissingtype
using StaticArrays: StaticVector, SVector, @SVector

using ...Theories
import ...Theories: ob, terminal, product, proj1, proj2, equalizer, incl,
  initial, coproduct, coproj1, coproj2, coequalizer, proj
using ..FreeDiagrams
import ..FreeDiagrams: apex, base, legs

# Data types
############

""" Abstract type for limit in a category.

The standard concrete subtype is [`Limit`](@ref), although for computational
reasons certain categories may use different subtypes to include extra data.
"""
abstract type AbstractLimit{Ob,Diagram} end

ob(lim::AbstractLimit) = apex(lim)
cone(lim::AbstractLimit) = lim.cone
apex(lim::AbstractLimit) = apex(cone(lim))
legs(lim::AbstractLimit) = legs(cone(lim))

Base.iterate(lim::AbstractLimit, args...) = iterate(cone(lim), args...)
Base.eltype(lim::AbstractLimit) = eltype(cone(lim))
Base.length(lim::AbstractLimit) = length(cone(lim))

""" Limit in a category.
"""
@auto_hash_equals struct Limit{Ob,Diagram,Cone<:Multispan{Ob}} <:
    AbstractLimit{Ob,Diagram}
  diagram::Diagram
  cone::Cone
end

const Terminal{Ob} = AbstractLimit{Ob,<:StaticVector{0}}
const BinaryProduct{Ob} = AbstractLimit{Ob,<:StaticVector{2}}
const Product{Ob} = AbstractLimit{Ob,<:AbstractVector}
const BinaryPullback{Ob} = AbstractLimit{Ob,<:Cospan}
const Pullback{Ob} = AbstractLimit{Ob,<:Multicospan}
const Equalizer{Ob} = AbstractLimit{Ob,<:ParallelMorphisms}

proj1(lim::Union{BinaryProduct,BinaryPullback}) = first(legs(lim))
proj2(lim::Union{BinaryProduct,BinaryPullback}) = last(legs(lim))
incl(eq::Equalizer) = only(legs(eq))

""" Abstract type for colimit in a category.

The standard concrete subtype is [`Colimit`](@ref), although for computational
reasons certain categories may use different subtypes to include extra data.
"""
abstract type AbstractColimit{Ob,Diagram} end

ob(colim::AbstractColimit) = base(colim)
cocone(colim::AbstractColimit) = colim.cocone
base(colim::AbstractColimit) = base(cocone(colim))
legs(colim::AbstractColimit) = legs(cocone(colim))

Base.iterate(colim::AbstractColimit, args...) = iterate(cocone(colim), args...)
Base.eltype(colim::AbstractColimit) = eltype(cocone(colim))
Base.length(colim::AbstractColimit) = length(cocone(colim))

""" Colimit in a category.
"""
@auto_hash_equals struct Colimit{Ob,Diagram,Cocone<:Multicospan{Ob}} <:
    AbstractColimit{Ob,Diagram}
  diagram::Diagram
  cocone::Cocone
end

const Initial{Ob} = AbstractColimit{Ob,<:StaticVector{0}}
const BinaryCoproduct{Ob} = AbstractColimit{Ob,<:StaticVector{2}}
const Coproduct{Ob} = AbstractColimit{Ob,<:AbstractVector}
const BinaryPushout{Ob} = AbstractColimit{Ob,<:Span}
const Pushout{Ob} = AbstractColimit{Ob,<:Multispan}
const Coequalizer{Ob} = AbstractColimit{Ob,<:ParallelMorphisms}

coproj1(colim::Union{BinaryCoproduct,BinaryPushout}) = first(legs(colim))
coproj2(colim::Union{BinaryCoproduct,BinaryPushout}) = last(legs(colim))
proj(coeq::Coequalizer) = only(legs(coeq))

# Specific (co)limits
#####################

terminal(T::Type) = product(@SVector T[])
initial(T::Type) = coproduct(@SVector T[])

""" Product of a pair of objects.
"""
product(A, B) = product(SVector(A, B))

""" Coproduct of a pair of objects.
"""
coproduct(A, B) = coproduct(SVector(A, B))

""" Equalizer of a pair of morphisms with common domain and codomain.
"""
equalizer(f, g) = equalizer(ParallelPair(f, g))
equalizer(fs::AbstractVector) = equalizer(ParallelMorphisms(fs))

""" Coequalizer of a pair of morphisms with common domain and codomain.
"""
coequalizer(f, g) = coequalizer(ParallelPair(f, g))
coequalizer(fs::AbstractVector) = coequalizer(ParallelMorphisms(fs))

""" Pullback of a pair of morphisms with common codomain.
"""
pullback(f, g) = pullback(Cospan(f, g))
pullback(fs::AbstractVector) = pullback(Multicospan(fs))

""" Pushout of a pair of morphisms with common domain.
"""
pushout(f, g) = pushout(Span(f, g))
pushout(fs::AbstractVector) = pushout(Multispan(fs))

""" Pullback of a cospan.

The default implementation computes the pullback from products and equalizers.
"""
function pullback(cospan::Cospan)
  f, g = cospan
  π1, π2 = product(dom(f), dom(g))
  ι = incl(equalizer(π1⋅f, π2⋅g))
  Limit(cospan, Span(ι⋅π1, ι⋅π2))
end

""" Pushout of a span.

The default implementation computes the pushout from coproducts and
coequalizers.
"""
function pushout(span::Span)
  f, g = span
  ι1, ι2 = coproduct(codom(f), codom(g))
  π = proj(coequalizer(f⋅ι1, g⋅ι2))
  Colimit(span, Cospan(ι1⋅π, ι2⋅π))
end

# General (co)limits
####################

# FIXME: Object type information should be encoded in C-set type.
limit(diagram::FreeDiagram) =
  limit(nonmissingtype(eltype(diagram.data.ob)), diagram)
colimit(diagram::FreeDiagram) =
  colimit(nonmissingtype(eltype(diagram.data.ob)), diagram)

end
