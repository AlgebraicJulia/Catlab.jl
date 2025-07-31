module Pushouts 
export ThCategoryWithPushouts, CatWithPushouts, pushout, composite_colimit, composite_universal, pushout_copair

using StructEquality
using GATlab

using ...Categories: Category, compose
using ...FreeDiagrams

using ..LimitsColimits: AbsColimit, ThCategoryColimitBase, ColimitCocone, 
                        CatWithCoequalizers, coproduct, coequalizer, factorize
import ..Colimits: diagram, universal, colimit

"""
Theory of unbiased pushouts, where `MSpan` is intended to be sent to multispans in the category.
"""
@theory ThCategoryWithPushouts <: ThCategoryColimitBase begin
  MSpan::TYPE{Multispan}

  colimit(d::MSpan)::Colimit
  universal(lim::Colimit, d::MSpan, sp::MCospan)::(ob(lim) → apex(sp))
end

ThCategoryWithPushouts.Meta.@wrapper CatWithPushouts

# Colimit data structures
#########################

""" Pushout formed as composite of coproduct and equalizer.

See also: [`CompositePullback`](@ref).
"""
struct CompositePushout{Hom} <: AbsColimit
  diagram::FreeDiagram
  cocone::Multicospan
  coprod::AbsColimit # ColimitCocone
  coeq::Hom
end

diagram(c::CompositePushout) = c.diagram

# TODO this should really take a wrapper for a theory which is the pushout of WithProducts and WithCoequalizers
function composite_colimit(m::CatWithCoequalizers, span::Multispan)
  𝒞 = getvalue(m)
  coprod = coproduct[𝒞](feet(span)...)
  (π,) = coeq = coequalizer[𝒞](map(compose[𝒞], legs(span), legs(coprod))...)
  cocone = Multicospan(map(ι -> compose(m, ι,π), legs(coprod)); cat=𝒞)
  CompositePushout(FreeDiagram(span), cocone, coprod, coeq)
end

function composite_universal(m::CatWithCoequalizers, lim::CompositePushout, 
                  cocone::Multicospan)
  factorize(m, lim.coeq, universal(m, lim.coprod, cocone))
end

# Named colimits and universal maps
###################################

@model_method pushout

pushout(C::CatWithPushouts, fs::AbstractVector) = 
  colimit[getvalue(C)](Multispan(fs; cat=getvalue(C)))

pushout(C::CatWithPushouts, f, g, fs...) = pushout(C, [f, g, fs...])

pushout(C::WithModel, fs::AbstractVector; context=nothing) = 
  colimit(C, Multispan(fs; cat=getvalue(C)); context)

pushout(C::WithModel, f, g, fs...; context=nothing) = 
  pushout(C, [f, g, fs...]; context)


@model_method pushout_copair

""" Pairing of morphisms: universal property of products/pullbacks.
"""
pushout_copair(C::CatWithPushouts, lim::AbsColimit, fs::AbstractVector) = 
  pushout_copair[getvalue(C)](lim, fs)

pushout_copair(C::CatWithPushouts, lim::AbsColimit, f1::T, f2::T) where {T} = 
  pushout_copair(C, lim, [f1, f2])

pushout_copair(m::WithModel, lim::AbsColimit, f1::T, f2::T; context=nothing) where T =
  pushout_copair(m, lim, [f1, f2]; context) 

pushout_copair(m::WithModel, lim::AbsColimit, fs::AbstractVector; context=nothing) = 
  universal(m, lim, Multicospan(fs); context)

end # module
