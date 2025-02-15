module Initials
export InitialColimit, ThCategoryWithInitial, CatWithInitial, create, initial

using StructEquality

using GATlab
using GATlab.Syntax.TheoryInterface: WithModel

import .....BasicSets: untag
import .....Theories: initial, create, □, universal, ob, ThCategory
import ...Functors: fmap
using ...FreeDiagrams
import ...FreeDiagrams: apex

using ..Colimits: AbsColimit, DefaultColimit, ThCategoryColimitBase
import ..Colimits: colimit, cocone, diagram

# Theory of categories with an initial object
#############################################

"""
`Initial` is expected to be implemented by `InitialColimit`.
"""
@theory ThCategoryWithInitial <: ThCategoryColimitBase begin
  Empty()::TYPE{EmptyDiagram}

  colimit(e::Empty)::Colimit
  universal(⊥::Colimit, e::Empty, csp::MCospan)::(ob(⊥) → apex(csp))
end

ThCategoryWithInitial.Meta.@wrapper CatWithInitial

# Named colimits and universal properties
#########################################
@model_method initial

initial(C::CatWithInitial) = initial[getvalue(C)]()

initial(m::WithModel; context=nothing) = 
  colimit(m, EmptyDiagram{impl_type(getvalue(m), ThCategory, :Ob)}())


@model_method create

create(C, x) = create[getvalue(C)](x)

function create(m::WithModel, x; context)
  O,H = impl_type.(Ref(getvalue(m)), Ref(ThCategory), [:Ob, :Hom])
  emp = EmptyDiagram{O}()
  universal(m, initial(m; context), emp, Multicospan{O,H,O}(x, H[], O[]); context)
end


# Special colimit data structures
#################################
""" Any implementation of a InitialColimit is just an object """
@struct_hash_equal struct InitialColimit{Ob,Hom} <: AbsColimit 
  ob::Ob
end

ob(i::InitialColimit) = i.ob

cocone(s::InitialColimit{Ob,Hom}) where {Ob, Hom} = 
  Multicospan{Ob,Hom,Ob}(s.ob, Hom[], Ob[])

diagram(::InitialColimit{Ob,Hom}) where {Ob,Hom} = 
  FreeDiagram(EmptyDiagram{Ob}())

fmap(i::InitialColimit, o, h, O, H) = InitialColimit{O,H}(o(i.ob))

untag(i::InitialColimit{Ob,Hom}, n::Int, m::Int) where {Ob,Hom} = 
  InitialColimit{untag(Ob,n), untag(Hom, m)}(untag(i.ob, n))

end # module
