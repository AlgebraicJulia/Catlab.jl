module Equalizers
export CompositeLimit, equalizer, factorize,  ThCategoryWithEqualizers, CatWithEqualizers

using StructEquality

using GATlab

using .....Theories: dom
import .....Theories: equalizer, factorize, universal, ob

using ..FreeDiagrams: Multispan, ParallelMorphisms

using ..Limits: AbsLimit, LimitCone
import ..Limits: limit
using ..Products: ThCategoryUnbiasedProducts

  
@theory ThCategoryWithEqualizers <: ThCategoryUnbiasedProducts begin
  ParallelDiagram()::TYPE # type of ParallelMorphisms
  limit(p::ParallelDiagram)::Limit
  universal(eq::Limit, p::ParallelDiagram, s::MSpan)::(apex(s) → ob(eq))
end

ThCategoryWithEqualizers.Meta.@wrapper CatWithEqualizers

# Named limits / universal properties
#####################################

equalizer(C::CatWithEqualizers, xs...) = equalizer[getvalue(C)](collect(xs))

equalizer(m::WithModel, d::AbstractVector; context=nothing) = 
  limit(m, ParallelMorphisms(d; cat=getvalue(m)); context)

""" Factor morphism through (co)equalizer, via the universal property.

To implement for equalizers of type `T`, define the method
`universal(::Equalizer{T}, ::SMultispan{1,T})`. For coequalizers of type `T`,
define the method `universal(::Coequalizer{T}, ::SMulticospan{1,T})`.
"""
function factorize(C::CatWithEqualizers, lim::AbsLimit, h)
  o = dom(C, h)
  universal(C, lim, Multispan(o, [h], [o]))
end

# Limit data structures 
#######################

""" Limit of general diagram computed by product-then-filter. """
@struct_hash_equal struct CompositeLimit{Hom} <: AbsLimit
  cone::Multispan
  prod::LimitCone
  incl::Hom
end

end # module
