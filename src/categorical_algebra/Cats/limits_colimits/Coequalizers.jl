module Coequalizers 
export coequalizer, CompositeColimit, CatWithCoequalizers, ThCategoryWithCoequalizers, factorize

using StructEquality
using GATlab

using .....Theories: codom
import .....Theories: proj, coequalizer, universal
using ..FreeDiagrams: ParallelMorphisms, Multicospan
using ..Colimits: AbsColimit, ColimitCocone, ThCategoryColimitBase
import ..Colimits: colimit
import ..Equalizers: factorize

@theory ThCategoryWithCoequalizers <: ThCategoryColimitBase begin
  ParallelDiagram()::TYPE{ParallelMorphisms}
  colimit(p::ParallelDiagram)::Colimit
  universal(eq::Colimit, p::ParallelDiagram, s::MCospan)::(ob(eq) → apex(s))
end

ThCategoryWithCoequalizers.Meta.@wrapper CatWithCoequalizers

# Named limits / universal properties
#####################################
@model_method coequalizer

coequalizer(C::CatWithCoequalizers, xs...) = 
  coequalizer[getvalue(C)](collect(xs))

coequalizer(m::WithModel, d::AbstractVector; context=nothing) = 
  colimit(m, ParallelMorphisms(d; cat=getvalue(m)); context)

coequalizer(m::WithModel, x, y, xs...; context=nothing) = 
  coequalizer(m, [x,y,xs...]; context)


function factorize(C::CatWithCoequalizers, lim::AbsColimit, h)
  o = codom(C, h)
  universal(C, lim, Multicospan(o, [h], [o]))
end

function factorize(C::WithModel, lim::AbsColimit, h; context=nothing)
  o = codom(C, h)
  universal(C, lim, Multicospan(o, [h], [o]))
end

""" Colimit of general diagram computed by coproduct and projection """
@struct_hash_equal struct CompositeColimit{Hom} <: AbsColimit
  cocone::Multicospan
  coprod::AbsColimit # ColimitCocone
  proj::Hom 
end

end # module
