module Pushouts 
export BinaryPushout, Pushout, pushout, BinaryCoequalizer, ComposeCoproductCoequalizer, coproj1, coproj2

import .....Theories: coproj1, coproj2, copair, ⋅, compose
using ...Cats, ...FreeDiagrams
using ..Colimits, ..Coproducts, ..Coequalizers
import ..Colimits: colimit, universal

const BinaryPushout{Ob} = AbstractColimit{Ob,<:Span}
const Pushout{Ob} = AbstractColimit{Ob,<:Multispan}


""" Compute pushout by composing a coproduct with a coequalizer.

See also: [`ComposeProductEqualizer`](@ref).
"""
struct ComposeCoproductCoequalizer <: ColimitAlgorithm end

""" Pushout formed as composite of coproduct and equalizer.

See also: [`CompositePullback`](@ref).
"""
struct CompositePushout{Ob, Diagram<:Multispan, Cocone<:Multicospan{Ob},
    Coprod<:Coproduct, Coeq<:Coequalizer} <: AbstractColimit{Ob,Diagram}
  diagram::Diagram
  cocone::Cocone
  coprod::Coprod
  coeq::Coeq
end

function colimit(span::Multispan, ::ComposeCoproductCoequalizer)
  coprod = coproduct(feet(span))
  (π,) = coeq = coequalizer(map(compose, legs(span), legs(coprod)))
  cocone = Multicospan(map(ι -> ι⋅π, legs(coprod)))
  CompositePushout(span, cocone, coprod, coeq)
end

function universal(lim::CompositePushout, cone::Multicospan)
  factorize(lim.coeq, universal(lim.coprod, cone))
end


""" Pushout of a pair of morphisms with common domain.

To implement for a type `T`, define the method `colimit(::Span{T})` and/or
`colimit(::Multispan{T})` or, if you have already implemented coproducts and
coequalizers, rely on the default implementation.
"""
pushout(f, g; kw...) = colimit(Span(f, g); kw...)
pushout(fs::AbstractVector; kw...) = colimit(Multispan(fs); kw...)

coproj1(colim::BinaryPushout) = first(legs(colim))
coproj2(colim::BinaryPushout) = last(legs(colim))


copair(colim::BinaryPushout, f, g) =
universal(colim, Cospan(f, g))
copair(colim::Pushout, fs::AbstractVector) =
universal(colim, Multicospan(fs))

end # module
