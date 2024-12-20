module Coequalizers 
export coequalizer, CompositeColimit

using StructEquality

import .....Theories: proj, coequalizer
using ..ParallelHoms: ParallelMorphisms
using ..Multispans: Multicospan
import ..LimitsColimits: universal
using ..Colimits: AbsColimit
using ..Coproducts: ThCategoryUnbiasedCoproducts, CoproductColimit

# coequalizer(f, g, model; alg=DefaultColimit()) = 
#   coequalizer([f,g], model; alg)

coequalizer(xs::AbstractVector, model) = #; alg=DefaultColimit()) = 
  colimit(ParallelMorphisms(xs), model, alg)


""" Colimit of general diagram computed by coproduct and projection """
@struct_hash_equal struct CompositeColimit{Hom} <: AbsColimit
  cocone::Multicospan
  coprod::CoproductColimit
  proj::Hom 
end

end # module
