module Equalizers 
export Equalizer, equalizer, incl, factorize

import .....Theories: incl, equalizer, factorize
using ...FreeDiagrams

using ..Limits

const BinaryEqualizer{Ob} = AbstractLimit{Ob,<:ParallelPair}
const Equalizer{Ob} = AbstractLimit{Ob,<:ParallelMorphisms}


""" Equalizer of morphisms with common domain and codomain.

To implement for a type `T`, define the method `limit(::ParallelPair{T})` and/or
`limit(::ParallelMorphisms{T})`.
"""
equalizer(f, g; kw...) = limit(ParallelPair(f, g); kw...)
equalizer(fs::AbstractVector; kw...) = limit(ParallelMorphisms(fs); kw...)

incl(eq::Equalizer) = only(legs(eq))


""" Factor morphism through (co)equalizer, via the universal property.

To implement for equalizers of type `T`, define the method
`universal(::Equalizer{T}, ::SMultispan{1,T})`. For coequalizers of type `T`,
define the method `universal(::Coequalizer{T}, ::SMulticospan{1,T})`.
"""
factorize(lim::Equalizer, h) = universal(lim, SMultispan{1}(h))
end # module
