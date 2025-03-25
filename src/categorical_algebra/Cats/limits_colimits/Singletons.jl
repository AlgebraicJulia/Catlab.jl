module Singletons 
export SingletonLimit, SingletonColimit

using .....Theories: id
using ...FreeDiagrams
using ..Limits, ..Colimits
import ..Limits: limit 
import ..Colimits: colimit
import ..LimitsColimits: universal, cone, cocone

""" Limit of a singleton diagram.
"""
struct SingletonLimit{Ob,Diagram<:SingletonDiagram{Ob}} <: AbstractLimit{Ob,Diagram}
  diagram::Diagram
end

cone(lim::SingletonLimit) = let x = only(lim.diagram)
  SMultispan{1}(x, id(x))
end

universal(::SingletonLimit, cone::Multispan) = only(cone)

limit(diagram::SingletonDiagram, ::SpecializeLimit) = SingletonLimit(diagram)

""" Colimit of a singleton diagram.
"""
struct SingletonColimit{Ob,Diagram<:SingletonDiagram{Ob}} <: AbstractColimit{Ob,Diagram}
  diagram::Diagram
end

cocone(colim::SingletonColimit) = let x = only(colim.diagram)
  SMulticospan{1}(x, id(x))
end

universal(::SingletonColimit, cocone::Multicospan) = only(cocone)

colimit(diagram::SingletonDiagram, ::SpecializeColimit) =
  SingletonColimit(diagram)

end # module
