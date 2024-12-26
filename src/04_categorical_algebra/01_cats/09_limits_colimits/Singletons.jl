module Singletons
export SingletonLimit, SingletonColimit

using StructEquality
using ...Categories: Category, id, ThCategory
using ...FreeDiagrams
import ...FreeDiagrams: ob
using ..Limits: AbsLimit
using ..Colimits: AbsColimit
import ..Limits: universal, limit, cone, legs

""" 
Special case when diagram is a singleton
"""
@struct_hash_equal struct SingletonLimit{Ob,Hom} <: AbsLimit
  ob::Ob
  i::Hom
  function SingletonLimit(m::Category, o::O) where O 
    i = ThCategory.id(m,o)
    new{O,typeof(i)}(o, i)
  end
end

ob(s::SingletonLimit) = s.ob

legs(s::SingletonLimit) = [s.i]

cone(s::SingletonLimit) = Multispan(ob(s), legs(s))

"""
In *any* category, we know how to construct the limit of a singleton diagram.
"""
limit(m::Category, d::SingletonDiagram) = SingletonLimit(m, only(d))

universal(::Category, ::SingletonLimit, cone::Multispan) = only(cone)

# Colimits
##########


""" 
Special case when diagram is a singleton
"""
@struct_hash_equal struct SingletonColimit{Ob,Hom} <: AbsColimit
  ob::Ob
  i::Hom
  function SingletonColimit(d::SingletonDiagram, o::O) where O
    i = id(m, o)
    new{O,typeof(i)}(o, i)
  end
end

ob(s::SingletonColimit) = s.ob

legs(s::SingletonColimit) = [s.i]

cocone(s::SingletonColimit)  = Multicospan(ob(s), legs(s))

"""
In *any* category, we know how to construct the limit of a singleton diagram.
"""
colimit(m::Category, d::SingletonDiagram) =
  Colimit(Diagram(d, m), SingletonColimit(d, m))

 universal(::Category,lim::SingletonColimit, cocone::Multicospan) = only(cocone)

end 