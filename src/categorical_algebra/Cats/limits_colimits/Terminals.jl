module Terminals 
export Terminal, terminal, delete

import .....Theories: delete, terminal
using ...FreeDiagrams

using ..Limits

""" Terminal object.

To implement for a type `T`, define the method `limit(::EmptyDiagram{T})`.
"""
terminal(T::Type; kw...) = limit(EmptyDiagram{T}(); kw...)

const Terminal{Ob} = AbstractLimit{Ob,<:EmptyDiagram}


""" Unique morphism into a terminal object.

To implement for a type `T`, define the method
`universal(::Terminal{T}, ::SMultispan{0,T})`.
"""
delete(A::T) where T = delete(terminal(T), A)
delete(lim::Terminal, A) = universal(lim, SMultispan{0}(A))

end # module
