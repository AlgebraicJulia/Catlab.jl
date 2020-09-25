""" Limits and colimits in a category.
"""
module Limits
export AbstractLimit, AbstractColimit, Limit, Colimit,
  ob, cone, cocone, apex, legs, limit, colimit, universal,
  Terminal, Initial, terminal, initial, delete, create, factorize,
  BinaryProduct, Product, product, proj1, proj2, pair,
  BinaryPullback, Pullback, BinaryEqualizer, Equalizer, pullback, incl,
  BinaryCoproduct, Coproduct, coproduct, coproj1, coproj2, copair,
  BinaryPushout, Pushout, BinaryCoequalizer, Coequalizer, pushout, proj,
  composite_pullback, composite_pushout

using Compat: only

using AutoHashEquals

using ...Theories
import ...Theories: ob, terminal, product, proj1, proj2, equalizer, incl,
  initial, coproduct, coproj1, coproj2, coequalizer, proj,
  delete, create, pair, copair, factorize
using ..FreeDiagrams
import ..FreeDiagrams: apex, legs

# Data types for limits
#######################

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

const Terminal{Ob} = AbstractLimit{Ob,<:EmptyDiagram}
const BinaryProduct{Ob} = AbstractLimit{Ob,<:ObjectPair}
const Product{Ob} = AbstractLimit{Ob,<:DiscreteDiagram}
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

ob(colim::AbstractColimit) = apex(colim)
cocone(colim::AbstractColimit) = colim.cocone
apex(colim::AbstractColimit) = apex(cocone(colim))
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

const Initial{Ob} = AbstractColimit{Ob,<:EmptyDiagram}
const BinaryCoproduct{Ob} = AbstractColimit{Ob,<:ObjectPair}
const Coproduct{Ob} = AbstractColimit{Ob,<:DiscreteDiagram}
const BinaryPushout{Ob} = AbstractColimit{Ob,<:Span}
const Pushout{Ob} = AbstractColimit{Ob,<:Multispan}
const BinaryCoequalizer{Ob} = AbstractColimit{Ob,<:ParallelPair}
const Coequalizer{Ob} = AbstractColimit{Ob,<:ParallelMorphisms}

coproj1(colim::Union{BinaryCoproduct,BinaryPushout}) = first(legs(colim))
coproj2(colim::Union{BinaryCoproduct,BinaryPushout}) = last(legs(colim))
proj(coeq::Coequalizer) = only(legs(coeq))

# Generic (co)limits
####################

""" Limit of a diagram.

To define limits in a category with objects `Ob`, override the method
`limit(::FreeDiagram{Ob})` for general limits or `limit(::D)` with suitable type
`D <: FixedShapeFreeDiagram{Ob}` for limits of specific shape, such as products
or equalizers.

See also: [`colimit`](@ref)
"""
function limit end

""" Colimit of a diagram.

To define colimits in a category with objects `Ob`, override the method
`colimit(::FreeDiagram{Ob})` for general colimits or `colimit(::D)` with
suitable type `D <: FixedShapeFreeDiagram{Ob}` for colimits of specific shape,
such as coproducts or coequalizers.

See also: [`limit`](@ref)
"""
function colimit end

""" Universal property of (co)limits.

Compute the morphism whose existence and uniqueness is guaranteed by the
universal property of (co)limits.

See also: [`limit`](@ref), [`colimit`](@ref).
"""
function universal end

# Specific (co)limits
#####################

""" Terminal object.

To implement for a type `T`, define the method `limit(::EmptyDiagram{T})`.
"""
terminal(T::Type) = limit(EmptyDiagram{T}())

""" Initial object.

To implement for a type `T`, define the method `colimit(::EmptyDiagram{T})`.
"""
initial(T::Type) = colimit(EmptyDiagram{T}())

""" Unique morphism into a terminal object.

To implement for a type `T`, define the method
`universal(::Terminal{T}, ::SMultispan{0,T})`.
"""
delete(lim::Terminal, A) = universal(lim, SMultispan{0}(A))

""" Unique morphism out of an initial object.

To implement for a type `T`, define the method
`universal(::Initial{T}, ::SMulticospan{0,T})`.
"""
create(colim::Initial, A) = universal(colim, SMulticospan{0}(A))

""" Product of objects.

To implement for a type `T`, define the method `limit(::ObjectPair{T})` and/or
`limit(::DiscreteDiagram{T})`.
"""
product(A, B) = limit(ObjectPair(A, B))
product(As::AbstractVector) = limit(DiscreteDiagram(As))

""" Coproduct of objects.

To implement for a type `T`, define the method `colimit(::ObjectPair{T})` and/or
`colimit(::DiscreteDiagram{T})`.
"""
coproduct(A, B) = colimit(ObjectPair(A, B))
coproduct(As::AbstractVector) = colimit(DiscreteDiagram(As))

""" Equalizer of morphisms with common domain and codomain.

To implement for a type `T`, define the method `limit(::ParallelPair{T})` and/or
`limit(::ParallelMorphisms{T})`.
"""
equalizer(f, g) = limit(ParallelPair(f, g))
equalizer(fs::AbstractVector) = limit(ParallelMorphisms(fs))

""" Coequalizer of morphisms with common domain and codomain.

To implement for a type `T`, define the method `colimit(::ParallelPair{T})` or
`colimit(::ParallelMorphisms{T})`.
"""
coequalizer(f, g) = colimit(ParallelPair(f, g))
coequalizer(fs::AbstractVector) = colimit(ParallelMorphisms(fs))

""" Pullback of a pair of morphisms with common codomain.

To implement for a type `T`, define the method `limit(::Cospan{T})` and/or
`limit(::Multicospan{T})` or, if you have already implemented products and
equalizers, rely on the default implementation.
"""
pullback(f, g) = limit(Cospan(f, g))
pullback(fs::AbstractVector) = limit(Multicospan(fs))

""" Pushout of a pair of morphisms with common domain.

To implement for a type `T`, define the method `colimit(::Span{T})` and/or
`colimit(::Multispan{T})` or, if you have already implemented coproducts and
coequalizers, rely on the default implementation.
"""
pushout(f, g) = colimit(Span(f, g))
pushout(fs::AbstractVector) = colimit(Multispan(fs))

""" Pairing of morphisms: universal property of products/pullbacks.

To implement for products of type `T`, define the method
`universal(::BinaryProduct{T}, ::Span{T})` and/or
`universal(::Product{T}, ::Multispan{T})` and similarly for pullbacks.
"""
pair(lim::Union{BinaryProduct,BinaryPullback}, f, g) =
  universal(lim, Span(f, g))
pair(lim::Union{Product,Pullback}, fs::AbstractVector) =
  universal(lim, Multispan(fs))

""" Copairing of morphisms: universal property of coproducts/pushouts.

To implement for coproducts of type `T`, define the method
`universal(::BinaryCoproduct{T}, ::Cospan{T})` and/or
`universal(::Coproduct{T}, ::Multicospan{T})` and similarly for pushouts.
"""
copair(colim::Union{BinaryCoproduct,BinaryPushout}, f, g) =
  universal(colim, Cospan(f, g))
copair(colim::Union{Coproduct,Pushout}, fs::AbstractVector) =
  universal(colim, Multicospan(fs))

""" Factor morphism through (co)equalizer, via the universal property.

To implement for equalizers of type `T`, define the method
`universal(::Equalizer{T}, ::SMultispan{1,T})`. For coequalizers of type `T`,
define the method `universal(::Coequalizer{T}, ::SMulticospan{1,T})`.
"""
factorize(lim::Equalizer, h) = universal(lim, SMultispan{1}(h))
factorize(colim::Coequalizer, h) = universal(colim, SMulticospan{1}(h))

# Composite (co)limits
######################

""" Pullback formed as composite of product and equalizer.

The fields of this struct are an implementation detail; accessing them directly
violates the abstraction. Everything that you can do with a pushout, including
invoking its universal property, should be done through the generic interface
for limits.

See also: [`CompositePushout`](@ref).
"""
struct CompositePullback{Ob, Diagram<:Multicospan{Ob}, Cone<:Multispan{Ob},
    Prod<:Product{Ob}, Eq<:Equalizer{Ob}} <: AbstractLimit{Ob,Diagram}
  diagram::Diagram
  cone::Cone
  prod::Prod
  eq::Eq
end

""" Compute pullback as composite of product and equalizer.
"""
function composite_pullback(cospan::Cospan)
  f, g = cospan
  (π1, π2) = prod = product(dom(f), dom(g))
  (ι,) = eq = equalizer(π1⋅f, π2⋅g)
  CompositePullback(cospan, Span(ι⋅π1, ι⋅π2), prod, eq)
end
composite_pullback(f, g) = composite_pullback(Cospan(f, g))

function universal(lim::CompositePullback, cone::Multispan)
  factorize(lim.eq, universal(lim.prod, cone))
end

""" Pushout formed as composite of coproduct and equalizer.

See also: [`CompositePullback`](@ref).
"""
struct CompositePushout{Ob, Diagram<:Multispan{Ob}, Cocone<:Multicospan{Ob},
    Coprod<:Coproduct{Ob}, Coeq<:Coequalizer{Ob}} <: AbstractColimit{Ob,Diagram}
  diagram::Diagram
  cocone::Cocone
  coprod::Coprod
  coeq::Coeq
end

""" Compute pushout as composite of coproduct and coequalizer.
"""
function composite_pushout(span::Span)
  f, g = span
  (ι1, ι2) = coprod = coproduct(codom(f), codom(g))
  (π,) = coeq = coequalizer(f⋅ι1, g⋅ι2)
  CompositePushout(span, Cospan(ι1⋅π, ι2⋅π), coprod, coeq)
end
composite_pushout(f, g) = composite_pushout(Span(f, g))

function universal(lim::CompositePushout, cone::Multicospan)
  factorize(lim.coeq, universal(lim.coprod, cone))
end

end
