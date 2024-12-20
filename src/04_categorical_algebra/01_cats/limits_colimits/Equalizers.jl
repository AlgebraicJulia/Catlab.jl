module Equalizers
export EqLimit, CompositeLimit, equalizer, factorize

using StructEquality

using GATlab

import .....Theories: equalizer
import ..FreeDiagrams: ob
using ..Multispans: Multispan
using ..ParallelHoms: ParallelMorphisms
using ..Limits: AbsLimit
import ..Limits: universal
using ..Products: ThCategoryUnbiasedProducts, ProductLimit


@struct_hash_equal struct EqLimit <: AbsLimit 
  incl::Any
end
  
@theory ThCategoryWithEqualizers <: ThCategoryUnbiasedProducts begin
  ParallelDiagram(pardom::Ob,parcod::Ob)::TYPE # type of ParallelMorphisms
  Equalizer(p::ParallelDiagram(a::Ob,b::Ob))::TYPE
  ob(eq::Equalizer(p))::Ob ⊣ [(a,b)::Ob, p::ParallelDiagram(a,b)]
  # We can't explicit explicitly represent proj functions of a DiscDiag
  universal(eq::Equalizer(d), s::(c→a))::(c → ob(eq)) ⊣ [
    (a,b,c)::Ob, d::ParallelDiagram(a,b)]
end

""" Factor morphism through (co)equalizer, via the universal property.

To implement for equalizers of type `T`, define the method
`universal(::Equalizer{T}, ::SMultispan{1,T})`. For coequalizers of type `T`,
define the method `universal(::Coequalizer{T}, ::SMulticospan{1,T})`.
"""
function factorize(lim::EqLimit, h)
  getvalue(lim.diag) isa ParallelMorphisms || error(
    "Can only call `factorize` on ParallelMorphisms colimits")
  universal(lim, Multispan(dom(h), [h]))
end

# equalizer(model::Category, f, g; alg=DefaultLimit()) = equalizer([f,g], model; alg)


# equalizer(model::Category, xs::AbstractVector; alg=DefaultLimit()) = 
#   limit(ParallelMorphisms(xs), model, alg)


# General limits 
################

""" Limit of general diagram computed by product-then-filter. """
@struct_hash_equal struct CompositeLimit{Hom} <: AbsLimit
  cone::Multispan
  prod::ProductLimit
  incl::EqLimit
end

end # module