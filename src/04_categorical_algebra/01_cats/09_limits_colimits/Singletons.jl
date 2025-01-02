module Singletons
export SingletonLimit, SingletonColimit

using StructEquality
using GATlab: WithModel, getvalue, @model_method

using ...Categories: Category, id, ThCategory
using ...FreeDiagrams
import ...FreeDiagrams: ob
using ..Limits: AbsLimit
using ..Colimits: AbsColimit
import ..Limits: universal, limit, cone, diagram
import ..Colimits: cocone, colimit


""" Limit of a singleton diagram.
"""
@struct_hash_equal struct SingletonLimit{Ob,Hom} <: AbsLimit
  x::Ob
  id_x::Hom
  SingletonLimit(x::Ob, m) where Ob = let i = id[m](x);
    new{Ob,typeof(i)}(x, i)
  end
end

function limit(m::WithModel, d::SingletonDiagram; context=nothing)
  x = only(d)
  SingletonLimit(x, getvalue(m))
end

cone(lim::SingletonLimit) = SMultispan{1}(lim.x, lim.id_x)

diagram(lim::SingletonLimit) = SingletonDiagram(lim.x)

@model_method universal
universal(::WithModel, ::SingletonLimit, f::Multispan) = only(f)


# Colimits
##########

""" Colimit of a singleton diagram.
"""
@struct_hash_equal struct SingletonColimit{Ob,Hom} <: AbsColimit
  x::Ob
  id_x::Hom
  SingletonColimit(x::Ob, m) where Ob = let i = id[m](x);
    new{Ob,typeof(i)}(x, i)
  end

end
function colimit(m, d::SingletonDiagram; context=nothing)
  x = only(d)
  SingletonColimit(x, m)
end


cocone(lim::SingletonColimit) = SMulticospan{1}(lim.x, lim.id_x)

diagram(lim::SingletonColimit) = SingletonDiagram(lim.ob)

universal(lim::SingletonColimit, ::Multicospan) = lim.id_x

end # module
