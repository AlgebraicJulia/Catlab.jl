module Pushouts 
export CompositePushout

using StructEquality
using GATlab

using ...Categories: Category
using ...FreeDiagrams

using ..Colimits: AbsColimit, ComposeCoproductCoequalizer
using ..Coproducts: CoproductColimit
# using ..Coequalizers: CoeqColimit


""" Pushout formed as composite of coproduct and equalizer.

See also: [`CompositePullback`](@ref).
"""
struct CompositePushout <: AbsColimit
  cocone::Multicospan
  coprod::CoproductColimit
  coeq::AbsColimit # CoeqColimit?
end

function colimit(span::Multispan, m::Category, ::ComposeCoproductCoequalizer)
  coprod = coproduct(feet(span), m)
  (π,) = coeq = coequalizer(map(compose[getvalue(m)], legs(span), legs(coprod)), m)
  cocone = Multicospan(map(ι -> compose(m, ι,π), legs(coprod)))
  Colimit(Diagram(span, m), CompositePushout(cocone, coprod, coeq))
end

function _universal(::Multispan, ::Category, lim::CompositePushout, 
                  cone::Multicospan)
  factorize(lim.coeq, universal(lim.coprod, cone))
end


pushout(fs::AbstractVector, model::Category; alg=DefaultColimit()) = 
  colimit(Multispan(fs), model, alg)

pushout(f,g, model::Category; alg=DefaultColimit()) = 
  colimit(Multispan([f,g]), model, alg)

end # module
