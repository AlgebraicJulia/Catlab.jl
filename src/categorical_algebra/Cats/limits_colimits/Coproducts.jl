module Coproducts 
export BinaryCoproduct, Coproduct, coproduct, coproj1, coproj2, copair

import .....Theories: coproj1, coproj2, coproduct, copair
using ...FreeDiagrams
using ..Colimits

const BinaryCoproduct{Ob} = AbstractColimit{Ob,<:ObjectPair}
const Coproduct{Ob} = AbstractColimit{Ob,<:DiscreteDiagram}

""" Coproduct of objects.

To implement for a type `T`, define the method `colimit(::ObjectPair{T})` and/or
`colimit(::DiscreteDiagram{T})`.
"""
coproduct(A, B; kw...) = colimit(ObjectPair(A, B); kw...)
coproduct(As::AbstractVector; kw...) = colimit(DiscreteDiagram(As); kw...)

coproj1(colim::BinaryCoproduct) = first(legs(colim))
coproj2(colim::BinaryCoproduct) = last(legs(colim))



""" Copairing of morphisms: universal property of coproducts/pushouts.

To implement for coproducts of type `T`, define the method
`universal(::BinaryCoproduct{T}, ::Cospan{T})` and/or
`universal(::Coproduct{T}, ::Multicospan{T})` and similarly for pushouts.
"""
copair(f, g) = copair(coproduct(dom(f), dom(g)), f, g)

copair(fs::AbstractVector) = copair(coproduct(map(dom, fs)), fs)

copair(colim::BinaryCoproduct, f, g) = universal(colim, Cospan(f, g))

copair(colim::Coproduct, fs::AbstractVector) = universal(colim, Multicospan(fs))


end # module
