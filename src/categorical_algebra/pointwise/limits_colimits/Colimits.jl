module Colimits 

export ACSetColimit

using StructEquality

using GATlab, ACSets

import .....Theories: ob
using .....BasicSets
using ....Cats, ....SetCats
import ....Cats: cone, cocone, diagram
using ...ACSetTransformations, ...CSets
using ...ACSetCats

using ..LimitsColimits: unpack, pack_components

using .ThHeteroMorphism: post

""" Limit of attributed C-sets that stores the pointwise limits in Set in 
addition to the usual data of the limit cone + original input diagram.
"""
@struct_hash_equal struct ACSetColimit <: AbsColimit
  cocone::Multicospan
  colimits::NamedTuple
  diagram::FreeDiagram
end

cocone(c::ACSetColimit) = c.cocone
ob(c::ACSetColimit) = apex(cocone(c))
diagram(c::ACSetColimit) = c.diagram

@instance ThCategoryWithInitial{ACSet,ACSetTransformation}  [model::ACSetCategory] begin

  colimit(d::EmptyDiagram) = pointwise_colimit(model, d)

  universal(lim::AbsColimit, ::EmptyDiagram, cocone::Multicospan) = 
    pointwise_universal(model, lim, cocone)
end

@instance ThCategoryUnbiasedCoproducts{ACSet,ACSetTransformation}  [model::ACSetCategory] begin

  colimit(d::DiscreteDiagram) = pointwise_colimit(model, d)

  universal(lim::AbsColimit, ::DiscreteDiagram, cocone::Multicospan) = 
    pointwise_universal(model, lim, cocone)
end  

@instance ThCategoryWithCoequalizers{ACSet,ACSetTransformation}  [model::ACSetCategory] begin 

  colimit(d::ParallelMorphisms) = pointwise_colimit(model, d)

  universal(lim::AbsColimit, ::ParallelMorphisms, cocone::Multicospan) = 
    pointwise_universal(model, lim, cocone)
end 

@instance ThCategoryWithPushouts{ACSet,ACSetTransformation}  [model::ACSetCategory] begin 

  colimit(d::Multispan) = pointwise_colimit(model, d)

  universal(lim::AbsColimit, ::Multispan, cocone::Multicospan) = 
    pointwise_universal(model, lim, cocone)
end 

@instance ThCategoryWithBipartiteColimits{ACSet,ACSetTransformation}  [model::ACSetCategory] begin 

  colimit(d::BipartiteFreeDiagram) = pointwise_colimit(model, d)

  universal(lim::AbsColimit, ::BipartiteFreeDiagram, cocone::Multicospan) = 
    pointwise_universal(model, lim, cocone)
end 


@instance ThCategoryWithColimits{ACSet,ACSetTransformation}  [model::ACSetCategory] begin 

  colimit(d::FreeGraph) = pointwise_colimit(model, d)

  universal(lim::AbsColimit, ::FreeGraph, cocone::Multicospan) = 
    pointwise_universal(model, lim, cocone)
end 


"""
Compute a limit in an ACSet category by pointwise limits for each object 
(in the entity category) and attrtype in the (in the attribute category).
"""
function pointwise_colimit(model, d)
  S, Fd = acset_schema(model), FreeDiagram(d)
  𝒞= CatWithCoproducts(entity_cat(model))
  # 𝒫 = prof_cat(model)
  upe, upa = unpack(model, Fd)
  ent_colimits = NamedTuple(map(ob(S)) do k
    k => colimit(𝒞, getvalue(upe[k]))
  end)
  attr_colimits = NamedTuple(map(attrtype(S)) do k
    𝒟 = CatWithCoproducts(attr_cat(model, k))
    k => colimit(𝒟, getvalue(upa[k])) 
  end)

  Xs = cocone_objects(d)
  ent_ιs = map(legs, ent_colimits)
  attr_ιs = map(legs, attr_colimits)
  Y = pointwise_colimit_apex(model, Xs, ent_colimits, attr_colimits, ent_ιs)
  ιs = pack_components(model, merge(ent_ιs, attr_ιs), Xs, map(X -> Y, Xs))
  ACSetColimit(Multicospan(Y, Vector{ACSetTransformation}(ιs)), merge(ent_colimits, attr_colimits), Fd)
end

"""
Apply colimit cocone's universal property to some cocone.
"""
function pointwise_universal(model::ACSetCategory, lim::AbsColimit, cone::Multicospan)
  S= acset_schema(model)
  𝒞 = entity_cat(model)
  upe, upa = unpack(model, FreeDiagram(cone))
  ent_components = Dict(map(ob(S)) do o
    o => universal[𝒞](lim.colimits[o], getvalue(upe[o]))
  end)
  attr_components = Dict(map(attrtype(S)) do o
    𝒟 = attr_cat(model, o)
    o => universal[𝒟](lim.colimits[o], getvalue(upa[o]))
  end)
  ACSetTransformation(merge(ent_components, attr_components), 
                      ob(lim), apex(cone); cat=model)
end

"""
Given colimits for each component, construct an ACSet that is the apex of the 
colimit cocone in the relevant category of ACSets and ACSet transformations.
"""
function pointwise_colimit_apex(C::ACSetCategory, Xs, 
    entity_colimits::NamedTuple, attr_colimits::NamedTuple, entity_ιs::NamedTuple)
  Y, S = constructor(C), acset_schema(C)
  𝒞 = entity_cat(C)
  for c in objects(S)
    add_parts!(Y, c, length(get_set(C, ob[𝒞](entity_colimits[c]))))
  end
  for d in attrtypes(S)
    𝒟 =attr_cat(C, d)
    add_parts!(Y, d, length(get_attr_set(C, ob[𝒟](attr_colimits[d]))))
  end
  for (f, c, d) in homs(S)
    Yfs = map((ι, X) -> compose[𝒞](get_hom(C, X, f), ι), legs(entity_colimits[d]), Xs)
    Yf = universal[𝒞](entity_colimits[c], Multicospan(ob(entity_colimits[d]), Yfs; cat=𝒞))
    set_subpart!(Y, f, collect(get_fn(C, Yf, get_ob(C, Y, c), get_ob(C, Y, d))))
  end

  for (f, c, d) in attrs(S)
    𝒫 = prof_cat(C, d)
    set_subpart!(Y, f, map(parts(Y, c)) do cᵢ
      res = []
      for (X, leg, ι) in zip(Xs, legs(attr_colimits[d]), entity_ιs[c])
        fun = get_attr_fn(C, post[𝒫](get_attr(C, X, f), leg), 
                          get_ob(C, Y, c), get_attrtype(C, Y, d))
        for p in preimage(ι, cᵢ)
          push!(res, fun(p))
        end
      end
      allequal(res) || error("Not all equal $res")
      val = first(res)
      return val
    end)
  end
  return Y
end

end # module
