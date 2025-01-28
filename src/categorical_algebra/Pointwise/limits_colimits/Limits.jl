module Limits 

export ACSetLimit

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
@struct_hash_equal struct ACSetLimit <: AbsLimit
  cone::Multispan
  limits::NamedTuple
  diagram::FreeDiagram
end

cone(c::ACSetLimit) = c.cone

ob(c::ACSetLimit) = apex(cone(c))

@instance ThCategoryWithTerminal{ACSet,ACSetTransformation,AbsSet, AbsLimit, 
    Multispan, EmptyDiagram}  [model::ACSetCategory] begin 

  limit(d::EmptyDiagram) = pointwise_limit(model, d)

  universal(lim::AbsLimit, ::EmptyDiagram, cone::Multispan) = 
    pointwise_universal(model, lim, cone)

end

@instance ThCategoryUnbiasedProducts{ACSet,ACSetTransformation,AbsSet, AbsLimit, 
    Multispan, DiscreteDiagram}  [model::ACSetCategory] begin 

  limit(d::DiscreteDiagram) = pointwise_limit(model, d)

  universal(lim::AbsLimit, ::DiscreteDiagram, cone::Multispan) = 
    pointwise_universal(model, lim, cone)

end 


@instance ThCategoryWithEqualizers{ACSet,ACSetTransformation,AbsSet, AbsLimit, 
    Multispan, ParallelMorphisms}  [model::ACSetCategory] begin 

  limit(d::ParallelMorphisms) = pointwise_limit(model, d)

  universal(lim::AbsLimit, ::ParallelMorphisms, cone::Multispan) = 
    pointwise_universal(model, lim, cone)
  
end 

@instance ThCategoryWithPullbacks{ACSet,ACSetTransformation,AbsSet, AbsLimit, 
    Multispan, Multicospan}  [model::ACSetCategory] begin 

  limit(d::Multicospan) = pointwise_limit(model, d)

  universal(lim::AbsLimit, ::Multicospan, cone::Multispan) = 
    pointwise_universal(model, lim, cone)
  
end 

@instance ThCategoryWithBipartiteLimits{ACSet,ACSetTransformation,AbsSet, AbsLimit, 
    Multispan, BipartiteFreeDiagram}  [model::ACSetCategory] begin 

  limit(d::BipartiteFreeDiagram) = pointwise_limit(model, d)

  universal(lim::AbsLimit, ::BipartiteFreeDiagram, cone::Multispan) = 
    pointwise_universal(model, lim, cone)
end 

@instance ThCategoryWithLimits{ACSet,ACSetTransformation,AbsSet, AbsLimit, 
    Multispan, FreeGraph}  [model::ACSetCategory] begin 

  limit(d::FreeGraph) = pointwise_limit(model, d)

  universal(lim::AbsLimit, ::FreeGraph, cone::Multispan) = 
    pointwise_universal(model, lim, cone)
end 


"""
Apply limit cone's universal property to some cone.
"""
function pointwise_universal(model::ACSetCategory, lim::AbsLimit, cone::Multispan)
  S= acset_schema(model)
  𝒞 = entity_cat(model)
  upe, upa = unpack(model, FreeDiagram(cone))
  comps = Dict(map(ob(S)) do o
    o => universal[𝒞](lim.limits[o], getvalue(upe[o]))
  end)
  acomps = Dict(map(attrtype(S)) do o 
    o => universal[𝒟](lim.limits[o], getvalue(upa[o]))
  end)
  ACSetTransformation(merge(comps, acomps), apex(cone), ob(lim); cat=model)
end

"""
Compute a limit in an ACSet category by pointwise limits for each object 
(in the entity category) and attrtype in the (in the attribute category).
"""
function pointwise_limit(model, d)
  S, Fd = acset_schema(model), FreeDiagram(d)
  𝒞 = CatWithProducts(entity_cat(model))
  upe, upa = unpack(model, Fd)
  limits_e = NamedTuple(map(collect(pairs(upe))) do (k, v)
    k => limit(𝒞, getvalue(v))
  end)
  limits_a = NamedTuple(map(collect(pairs(upa))) do (k, v)
    𝒟 = CatWithProducts(attr_cat(model, o))
    k => limit(𝒟, getvalue(v))
  end)
  Xs = cone_objects(d)
  πs_e = map(legs, limits_e)
  πs_a = NamedTuple(map(attrs(S)) do (f,c,d) 
    d => map(zip(Xs, legs(attr_colimits[d]))) do (X,ι)
      post[𝒫](get_attr(model, X, f), ι)
    end
  end)

  Y = pointwise_limit_apex(model, Xs, limits_e, limits_a, πs_e)
  πs = pack_components(model, merge(πs_e, πs_a), map(X -> Y, Xs), Xs)
  ACSetLimit(Multispan(Y, Vector{ACSetTransformation}(πs)), merge(limits_e, limits_a), Fd)
end

"""
Given limits for each component, construct an ACSet that is the apex of the 
limit cone in the relevant category of ACSets and ACSet transformations.
"""
function pointwise_limit_apex(C::ACSetCategory, Xs, entity_limits::NamedTuple, 
                              attr_limits::NamedTuple, ιs::NamedTuple)
  Y, S = constructor(C), acset_schema(C)
  𝒞 = CatWithProducts(entity_cat(C))
  for c in objects(S)
    add_parts!(Y, c, length(ob(𝒞, entity_limits[c])))
  end
  for (f, c, d) in homs(S)
    Yfs = map((π, X) -> compose(𝒞, π,  get_hom(C, X, f)), legs(entity_limits[c]), Xs
             ) |> Vector{impl_type(𝒞, :Hom)}
    sp = Multispan(ob(𝒞, entity_limits[c]), Yfs; cat=getvalue(𝒞))
    Yf = universal(𝒞, entity_limits[d], sp)
    set_subpart!(Y, f, collect(Yf))
  end
  return Y
end


end # module