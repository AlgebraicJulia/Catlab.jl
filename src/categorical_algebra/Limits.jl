""" Limits and colimits in a category.
"""
module Limits
export AbstractLimit, AbstractColimit, Limit, Colimit,
  ob, cone, cocone, apex, base, legs, limit, colimit, factorize,
  Terminal, Initial, terminal, initial, delete, create,
  BinaryProduct, Product, product, proj1, proj2, pair,
  BinaryPullback, Pullback, BinaryEqualizer, Equalizer, pullback, incl,
  BinaryCoproduct, Coproduct, coproduct, coproj1, coproj2, copair,
  BinaryPushout, Pushout, BinaryCoequalizer, Coequalizer, pushout, proj

using Compat: only

using AutoHashEquals
using StaticArrays: StaticVector, SVector, @SVector

using ...Theories
import ...Theories: ob, terminal, product, proj1, proj2, equalizer, incl,
  initial, coproduct, coproj1, coproj2, coequalizer, proj,
  factorize, delete, create, pair, copair
using ..FreeDiagrams
import ..FreeDiagrams: apex, base, legs

# Data types for limits
#######################

""" Abstract type for limit in a category.

The standard concrete subtype is [`Limit`](@ref), although for computational
reasons certain categories may use different subtypes to include extra data.
"""
abstract type AbstractLimit{Ob,Diagram} end

diagram(lim::AbstractLimit) = lim.diagram
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
const BinaryEqualizer{Ob} = AbstractLimit{Ob,<:ParallelPair}
const Equalizer{Ob} = AbstractLimit{Ob,<:ParallelMorphisms}

proj1(lim::Union{BinaryProduct,BinaryPullback}) = first(legs(lim))
proj2(lim::Union{BinaryProduct,BinaryPullback}) = last(legs(lim))
incl(eq::Equalizer) = only(legs(eq))

# Data types for colimits
#########################

""" Abstract type for colimit in a category.

The standard concrete subtype is [`Colimit`](@ref), although for computational
reasons certain categories may use different subtypes to include extra data.
"""
abstract type AbstractColimit{Ob,Diagram} end

diagram(lim::AbstractColimit) = lim.diagram
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
const BinaryCoequalizer{Ob} = AbstractColimit{Ob,<:ParallelPair}
const Coequalizer{Ob} = AbstractColimit{Ob,<:ParallelMorphisms}

coproj1(colim::Union{BinaryCoproduct,BinaryPushout}) = first(legs(colim))
coproj2(colim::Union{BinaryCoproduct,BinaryPushout}) = last(legs(colim))
proj(coeq::Coequalizer) = only(legs(coeq))

# Generic functions
###################

""" Limit of a diagram.
"""
function limit end

""" Colimit of a diagram.
"""
function colimit end

terminal(T::Type) = product(@SVector T[])
initial(T::Type) = coproduct(@SVector T[])

delete(lim::Terminal, A) = factorize(lim, A)
create(colim::Initial, A) = factorize(colim, A)

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

""" Pairing of morphisms: universal property of products/pullbacks.
"""
pair(lim::Union{BinaryProduct,BinaryPullback}, f, g) =
  factorize(lim, Span(f, g))
pair(lim::Union{Product,Pullback}, fs::AbstractVector) =
  factorize(lim, Multispan(fs))

""" Copairing of morphisms: universal property of coproducts/pushouts.
"""
copair(colim::Union{BinaryCoproduct,BinaryPushout}, f, g) =
  factorize(colim, Cospan(f, g))
copair(colim::Union{Coproduct,Pushout}, fs::AbstractVector) =
  factorize(colim, Multicospan(fs))

# Default implementations
#########################

""" Pullback formed as composite of product and equalizer.
"""
struct CompositePullback{Ob, Diagram<:Multicospan{Ob}, Cone<:Multispan{Ob},
    Prod<:Product{Ob}, Eq<:Equalizer{Ob}} <: AbstractLimit{Ob,Diagram}
  diagram::Diagram
  cone::Cone
  prod::Prod
  eq::Eq
end

""" Pullback of a cospan.

The default implementation computes the pullback from products and equalizers.
"""
function pullback(cospan::Cospan)
  f, g = cospan
  (π1, π2) = prod = product(dom(f), dom(g))
  (ι,) = eq = equalizer(π1⋅f, π2⋅g)
  CompositePullback(cospan, Span(ι⋅π1, ι⋅π2), prod, eq)
end

function factorize(lim::CompositePullback, fs::Multispan)
  factorize(lim.eq, factorize(lim.prod, fs))
end

""" Pushout formed as composite of coproduct and equalizer.
"""
struct CompositePushout{Ob, Diagram<:Multispan{Ob}, Cocone<:Multicospan{Ob},
    Coprod<:Coproduct{Ob}, Coeq<:Coequalizer{Ob}} <: AbstractColimit{Ob,Diagram}
  diagram::Diagram
  cocone::Cocone
  coprod::Coprod
  coeq::Coeq
end

""" Pushout of a span.

The default implementation computes the pushout from coproducts and
coequalizers.
"""
function pushout(span::Span)
  f, g = span
  (ι1, ι2) = coprod = coproduct(codom(f), codom(g))
  (π,) = coeq = coequalizer(f⋅ι1, g⋅ι2)
  CompositePushout(span, Cospan(ι1⋅π, ι2⋅π), coprod, coeq)
end

function factorize(lim::CompositePushout, fs::Multicospan)
  factorize(lim.coeq, factorize(lim.coprod, fs))
end

end
