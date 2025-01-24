module Initials 
export Initial, initial, create

import .....Theories: initial, create
using ...FreeDiagrams
using ..Colimits

const Initial{Ob} = AbstractColimit{Ob,<:EmptyDiagram}


""" Initial object.

To implement for a type `T`, define the method `colimit(::EmptyDiagram{T})`.
"""
initial(T::Type; kw...) = colimit(EmptyDiagram{T}(); kw...)



""" Unique morphism out of an initial object.

To implement for a type `T`, define the method
`universal(::Initial{T}, ::SMulticospan{0,T})`.
"""
create(A::T) where T = create(initial(T), A)
create(colim::Initial, A) = universal(colim, SMulticospan{0}(A))


end # module
