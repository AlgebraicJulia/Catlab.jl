module Colimits 

export ACSetColimit

using StructEquality

using GATlab, ACSets
using ACSets.DenseACSets: attrtype_type

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
Compute a colimit in an ACSet category by pointwise colimits for each object 
(in the entity category) and attrtype in the (in the attribute category).
"""
function pointwise_colimit(model::ACSetCategory, diagram)
  # Unpack input data
  S, FreeD = acset_schema(model), FreeDiagram(diagram)
  Xs = cocone_objects(diagram)
  Ob, Attr = ob(S), attrtype(S)
  entities_pointwise, attrtypes_pointwise = unpack(model, FreeD)
  𝒞 = entity_cat(model)

  # Compute pointwise colimits 
  ent_colims = NamedTuple(map(Ob) do obj
    obj => colimit[𝒞](getvalue(entities_pointwise[obj]))
  end)

  attr_colims = NamedTuple(map(Attr) do i
    𝒟ᵢ = attr_cat(model, i)
    i => colimit[𝒟ᵢ](getvalue(attrtypes_pointwise[i])) 
  end)

  colimits = merge(ent_colims, attr_colims)
  
  # Compute apex of the colimit
  to_skel(clim) = map(ι -> postcompose(ι, skel(codom(ι))), legs(clim))
  entity_incls = NamedTuple(k => to_skel(v) for (k, v) in pairs(ent_colims))

  Y = pointwise_colimit_apex(model, Xs, ent_colims, attr_colims, entity_incls)

  # Compute maps from objects of diagram into apex of colimit
  attr_incls = NamedTuple(map(collect(pairs(attr_colims))) do (i, colim)
    𝒟ᵢ = attr_cat(model, i)
    cod_int_set = ob_map[𝒟ᵢ](get_attrtype(model, Y, i)) # Left{Int}+Right{T} set
    i => map(zip(Xs, legs(colim))) do (X, ι) 
      fnι = hom_map[𝒟ᵢ](ι) # interpret i-component as a function into coproduct
      var_set = left(getvalue(codom(fnι))) # set of not-necessarily-integer vars
      to_int = pure(skel(var_set), attrtype_type(Y, i))
      postcompose(fnι, SetFunction(CopairedFinDomFunction(to_int)))
    end
  end) 

  incls = merge(entity_incls, attr_incls)
  ιs = pack_components(model, incls, Xs, map(_ -> Y, Xs)
                      ) |> Vector{ACSetTransformation}

  ACSetColimit(Multicospan(Y, ιs), colimits, FreeD)
end

"""
Given a colimit Aᵢ⇉ΣAᵢ colimit cocone's universal property to some cocone Aᵢ⇉ X 
to get a map ΣAᵢ → X 
"""
function pointwise_universal(model::ACSetCategory, lim::AbsColimit, 
                             cone::Multicospan)
  S= acset_schema(model)
  Ob = ob(S)
  𝒞 = entity_cat(model)
  upe, upa = unpack(model, FreeDiagram(cone))

  ent_components = Dict(map(Ob) do o
    u = universal[𝒞](lim.colimits[o], getvalue(upe[o]))
    d, cd = get_ob(model, apex(lim), o), dom[𝒞](u)
    pre = from_skel(dom(u))
    u′ = compose[𝒞](pre, u)
    o => u′
  end)

  # Apply the universal property to each attrtype pointwise
  attr_components = Dict(map(attrtype(S)) do o
    𝒟 = attr_cat(model, o)
    res = universal[𝒟](lim.colimits[o], getvalue(upa[o]))
    o => res
  end)

  ACSetTransformation(merge(ent_components, attr_components), 
                      ob(lim), apex(cone); cat=model)
end

from_skel(s::FinSet) = FinFunction(Dict(enumerate(s)), FinSet(length(s)), s)

skel(s::FinSet) = FinFunction(Dict(reverse.(enumerate(s))), s, FinSet(length(s)))

"""
Given colimits for each component, construct an ACSet that is the apex of the 
colimit cocone in the relevant category of ACSets and ACSet transformations.
"""
function pointwise_colimit_apex(C::ACSetCategory, Xs, 
    entity_colimits::NamedTuple, attr_colimits::NamedTuple, 
    entity_ιs::NamedTuple)#; finset_mapping)
  Y, S = constructor(C), acset_schema(C)
  𝒞 = entity_cat(C)
  W𝒞 = GATlab.WithModel(𝒞)
  for o in objects(S)
    add_parts!(Y, o, length(ob_map(W𝒞, apex(entity_colimits[o]))))
  end

  for d in attrtypes(S)
    𝒟 = attr_cat(C, d)
    s = getvalue(ob_map[𝒟](ob[𝒟](attr_colimits[d])))
    s isa EitherSet || error("Must be EitherSet: $s")
    add_parts!(Y, d, length(left(s)))
  end
  for (f, c, d) in homs(S)
    Yfs = map((ι, X) -> compose(W𝒞, get_hom(C, X, f), ι), 
              legs(entity_colimits[d]), Xs)
    Yf = universal(W𝒞, entity_colimits[c], 
                   Multicospan(ob(entity_colimits[d]), Yfs; cat=𝒞))
    c_skel⁻¹ = from_skel(ob_map[𝒞](apex(entity_colimits[c])))
    d_skel = skel(ob_map[𝒞](apex(entity_colimits[d])))
    fYf = postcompose(c_skel⁻¹, postcompose(hom_map[𝒞](Yf), d_skel))
    for pᶜ in parts(Y,c)
      set_subpart!(Y, pᶜ, f, fYf(pᶜ))
    end
  end
  for (f, c, d) in attrs(S)
    𝒫 = prof_cat(C, d)
    𝒟 = attr_cat(C, d)
    d_skel = skel(left(getvalue(ob_map[𝒟](apex(attr_colimits[d])))))
    # Compute legs
    leg_funs = map(zip(Xs, legs(attr_colimits[d]))) do (X, leg)
      post[𝒫](get_attr(C, X, f), leg)
    end
    for cᵢ in parts(Y, c)
      res = []
      for (leg_fun, ι) in zip(leg_funs, entity_ιs[c])
        for p in preimage(ι, cᵢ)
          push!(res, hom_map[𝒫](leg_fun)(Left(p)))
        end
      end
      allequal(res) || error("Not all equal $res")
      val = if first(res) isa Right 
        getvalue(first(res))
      elseif first(res) isa Left
        AttrVar(d_skel(getvalue(first(res))))
      else 
        error("Expected $(first(res))::$(typeof(first(res))) to be Left or Right")
      end
      set_subpart!(Y, cᵢ, f,  val)
    end
  end
  return Y
end

end # module
