module Colimits 

export ACSetColimit

using StructEquality

using GATlab, ACSets

import .....Theories: ob
using .....BasicSets
using ....Cats, ....SetCats
import ....Cats: cone, cocone
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

@instance ThCategoryWithCoequalizers{ACSet,ACSetTransformation,AbsSet, AbsColimit, 
                                 Multicospan, EmptyDiagram, DiscreteDiagram, ParallelMorphisms
    }  [model::ACSetCategory
        ] begin 

  colimit(d::EmptyDiagram) = pointwise_colimit(model, d)

  universal(lim::AbsColimit, ::EmptyDiagram, cocone::Multicospan) = 
    pointwise_universal(model, lim, cocone)

  colimit(d::DiscreteDiagram) = pointwise_colimit(model, d)

  universal(lim::AbsColimit, ::DiscreteDiagram, cocone::Multicospan) = 
    pointwise_universal(model, lim, cocone)

  colimit(d::ParallelMorphisms) = pointwise_colimit(model, d)

  universal(lim::AbsColimit, ::ParallelMorphisms, cocone::Multicospan) = 
    pointwise_universal(model, lim, cocone)
  
  # Etc: can do all colimits this way
end 

"""
Compute a limit in an ACSet category by pointwise limits for each object 
(in the entity category) and attrtype in the (in the attribute category).
"""
function pointwise_colimit(model, d)
  S, Fd = acset_schema(model), FreeDiagram(d)
  𝒞, 𝒟 = CatWithCoproducts(entity_cat(model)), CatWithCoproducts(attr_cat(model))
  𝒫 = prof_cat(model)
  upe, upa = unpack(model, Fd)
  ent_colimits = NamedTuple(map(ob(S)) do k
    k => colimit(𝒞, getvalue(upe[k]))
  end)
  attr_colimits = NamedTuple(map(attrtype(S)) do k
    k => colimit(𝒟, getvalue(upa[k]))
  end)

  Xs = cocone_objects(d)
  ent_ιs = map(legs, ent_colimits)
  attr_ιs = NamedTuple(map(attrs(S)) do (f,c,d) 
    d => map(zip(Xs, legs(attr_colimits[d]))) do (X,ι)
      post[𝒫](get_attr(model, X, f), ι)
    end
  end)
  Y = pointwise_colimit_apex(model, Xs, ent_colimits, attr_colimits, ent_ιs)
  ιs = pack_components(model, merge(ent_ιs, attr_ιs), Xs, map(X -> Y, Xs))
  ACSetColimit(Multicospan(Y, Vector{ACSetTransformation}(ιs)), merge(ent_colimits, attr_colimits), Fd)
end

"""
Apply limit cone's universal property to some cone.
"""
function pointwise_universal(model::ACSetCategory, lim::AbsColimit, cone::Multicospan)
  S= acset_schema(model)
  𝒞, 𝒟 = entity_cat(model), attr_cat(model)
  upe, upa = unpack(model, FreeDiagram(cone))
  ent_components = Dict(map(ob(S)) do o  # TODO also do this for the attr_cat
    o => universal[𝒞](lim.colimits[o], getvalue(upe[o]))
  end)
  attr_components = Dict(map(attrtype(S)) do o
    o => universal[𝒟](lim.colimits[o], getvalue(upa[o]))
  end)
  ACSetTransformation(merge(ent_components, attr_components), 
                      ob(lim), apex(cone), model)
end

"""
Given limits for each component, construct an ACSet that is the apex of the 
limit cone in the relevant category of ACSets and ACSet transformations.
"""
function pointwise_colimit_apex(C::ACSetCategory, Xs, 
    entity_colimits::NamedTuple, attr_colimits::NamedTuple, entity_ιs::NamedTuple)
  Y, S = constructor(C), acset_schema(C)
  𝒞, 𝒟, 𝒫 = entity_cat(C), attr_cat(C), prof_cat(C)
  for c in objects(S)
    add_parts!(Y, c, length(get_set(C, ob[𝒞](entity_colimits[c]))))
  end
  for d in attrtypes(S)
    add_parts!(Y, d, length(get_attr_set(C, ob[𝒟](attr_colimits[d]))))
  end
  for (f, c, d) in homs(S)
    Yfs = map((ι, X) -> compose[𝒞](get_hom(C, X, f), ι), legs(entity_colimits[d]), Xs)
    Yf = universal[𝒞](entity_colimits[c], Multicospan(ob(entity_colimits[d]), Yfs; cat=𝒞))
    set_subpart!(Y, f, collect(get_fn(C, Yf)))
  end

  for (f, c, d) in attrs(S)
    set_subpart!(Y, f, map(parts(Y, c)) do cᵢ
      res = []
      for (X, leg, ι) in zip(Xs, legs(attr_colimits[d]), entity_ιs[c])
        fun = get_attr_fn(C, post[𝒫](get_attr(C, X, f), leg))
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
