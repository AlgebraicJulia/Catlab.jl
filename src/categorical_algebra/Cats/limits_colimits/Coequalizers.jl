module Coequalizers 
export BinaryCoequalizer, Coequalizer, coequalizer, proj, factorize

import .....Theories: proj, coequalizer, factorize
using ...FreeDiagrams
using ..Colimits


const BinaryCoequalizer{Ob} = AbstractColimit{Ob,<:ParallelPair}
const Coequalizer{Ob} = AbstractColimit{Ob,<:ParallelMorphisms}


""" Coequalizer of morphisms with common domain and codomain.

To implement for a type `T`, define the method `colimit(::ParallelPair{T})` or
`colimit(::ParallelMorphisms{T})`.
"""
coequalizer(f, g; kw...) = colimit(ParallelPair(f, g); kw...)
coequalizer(fs::AbstractVector; kw...) = colimit(ParallelMorphisms(fs); kw...)

proj(coeq::Coequalizer) = only(legs(coeq))


factorize(colim::Coequalizer, h) = universal(colim, SMulticospan{1}(h))

end # module
