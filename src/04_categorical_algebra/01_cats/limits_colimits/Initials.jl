module Initials
export InitialColimit, ThCategoryWithInitial, CatWithInitial, create, initial

using StructEquality

using GATlab
using GATlab.Syntax.TheoryInterface: WithModel

import .....Theories: initial, create, □, universal, ob
using ...Categories: Category
using ...FreeDiagrams

using ..Colimits: AbsColimit, DefaultColimit
import ..Colimits: colimit, cocone

"""
`Initial` is expected to be implemented by `InitialColimit`.
"""
@theory ThCategoryWithInitial <: ThCategory begin
  Initial()::TYPE
  initial()::Initial()
  ob(⊥::Initial())::Ob
  universal(⊥::Initial(), C::Ob)::(ob(⊥) → C)

  □(C::Ob)::(ob(initial())→C) # := create(initial(), C) TODO implement AlgFun
end

create(C, x) = universal(C, initial(C), x)

# hack this into every model (still need to @import it)
□(m::WithModel, x; context) = create(m, initial(m; context), x; context)


ThCategoryWithInitial.Meta.@wrapper CatWithInitial

""" Any implementation of a InitialColimit is just an object """
@struct_hash_equal struct InitialColimit{Ob,Hom} <: AbsColimit 
  ob::Ob
end

cocone(s::InitialColimit{Ob,Hom}) where {Ob, Hom} = Multicospan(s.ob, Hom[])


colimit(c::CatWithInitial, ::EmptyDiagram) = initial(c)


end # module
