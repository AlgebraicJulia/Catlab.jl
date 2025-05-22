module Singletons
export SingletonLimit, SingletonColimit

using StructEquality
using GATlab

using ...Categories, ...FreeDiagrams, ..Limits, ..Colimits
import ..Limits: universal, limit, cone, diagram, ob
import ..Colimits: cocone, colimit

"""
`Sing` is expected to be implemented by `SingletonDiagram`.
"""
@theory ThCategoryWithSingletonLimits <: ThCategoryLimitBase begin
  Sing()::TYPE{SingletonDiagram}
  limit(e::Sing)::Limit
  universal(lim::Limit, d::Sing, sp::MSpan)::(apex(sp) → ob(lim))
end


""" Limit of a singleton diagram.
"""
@struct_hash_equal struct SingletonLimit{Ob,Hom} <: AbsLimit
  x::Ob
  id_x::Hom
  SingletonLimit(x::Ob, m::TypeCat{Ob,Hom}) where {Ob,Hom} =
    new{Ob,Hom}(x, id(m, x))
end

ob(s::SingletonLimit) = s.x
cone(s::SingletonLimit) = SMultispan{1}(s.id_x)
diagram(s::SingletonLimit) = FreeDiagram(SingletonDiagram(s.x))

@instance ThCategoryWithSingletonLimits{Ob, Hom
                                       } [model::TypeCat{Ob,Hom}
                                         ]where {Ob,Hom} begin 
  limit(d::SingletonDiagram) = SingletonLimit(only(d), model)
  universal(::AbsLimit, ::SingletonDiagram, sp::Multispan) = only(sp)
end


# Colimits
##########

"""
`Sing` is expected to be implemented by `SingletonDiagram`.
"""
@theory ThCategoryWithSingletonColimits <: ThCategoryColimitBase begin
  Sing()::TYPE{SingletonDiagram}
  colimit(e::Sing)::Colimit
  universal(lim::Colimit, d::Sing, sp::MCospan)::(ob(lim) → apex(sp))
end


""" Colimit of a singleton diagram.
"""
@struct_hash_equal struct SingletonColimit{Ob,Hom} <: AbsColimit
  x::Ob
  id_x::Hom
  SingletonColimit(x::Ob, m::TypeCat{Ob,Hom}) where {Ob,Hom} =
    new{Ob,Hom}(x, id(m, x))
end

ob(s::SingletonColimit) = s.x
cone(s::SingletonColimit) = SMultispan{1}(s.id_x)
diagram(s::SingletonColimit) = FreeDiagram(SingletonDiagram(s.x))

@instance ThCategoryWithSingletonColimits{Ob, Hom
                                          } [model::TypeCat{Ob,Hom}
                                            ]where {Ob,Hom} begin 
  colimit(d::SingletonDiagram) = SingletonColimit(only(d), model)
  universal(::AbsColimit, ::SingletonDiagram, sp::Multicospan) = only(sp)
end

end # module
