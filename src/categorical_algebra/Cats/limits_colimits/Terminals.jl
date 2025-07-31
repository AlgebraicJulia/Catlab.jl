module Terminals 
export TerminalLimit, ThCategoryWithTerminal, CatWithTerminal, delete, terminal

using StructEquality

using GATlab

import .....Theories: terminal, delete, ◊, universal, ob, ThCategory
using ...FreeDiagrams
import ...FreeDiagrams: EmptyDiagram, apex
using ..Limits: AbsLimit, DefaultLimit, ThCategoryLimitBase
import ..Limits: limit, cone, diagram


"""
`Terminal` is expected to be implemented by `TerminalLimit`.
"""
@theory ThCategoryWithTerminal <: ThCategoryLimitBase begin
  Empty()::TYPE{EmptyDiagram}
  limit(e::Empty)::Limit
  universal(lim::Limit, d::Empty, sp::MSpan)::(apex(sp) → ob(lim))
end

ThCategoryWithTerminal.Meta.@wrapper CatWithTerminal


# Named limits / universal properties
#####################################
@model_method terminal

terminal(C::CatWithTerminal) = terminal[getvalue(C)]()

terminal(m::WithModel; context=nothing) = 
  limit(m, EmptyDiagram{impl_type(getvalue(m), ThCategory, :Ob)}(); context)

@model_method delete

delete(C, x) = delete[getvalue(C)](x)

function delete(m::WithModel, x; context)
  O, H = impl_types(getvalue(m), ThCategory)
  emp = EmptyDiagram{O}()
  universal(m, terminal(m; context), emp, Multispan{O,H,O}(x, H[], O[]); context)
end

# Special limit data structure
##############################

""" Any implementation of a TerminalLimit is just an object """
@struct_hash_equal struct TerminalLimit{Ob,Hom} <: AbsLimit 
  ob::Ob
end

ob(t::TerminalLimit) = t.ob

cone(s::TerminalLimit{Ob,Hom}) where {Ob, Hom} = 
  Multispan(s.ob, Hom[], Ob[])

diagram(::TerminalLimit{Ob,Hom}) where {Ob,Hom} = 
  FreeDiagram(EmptyDiagram{Ob}())

end # module
