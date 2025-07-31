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

@instance ThCategoryWithTerminal{ACSet,ACSetTransformation}  [model::ACSetCategory] begin 

  limit(d::EmptyDiagram) = pointwise_limit(model, d)

  universal(lim::AbsLimit, ::EmptyDiagram, cone::Multispan) = 
    pointwise_universal(model, lim, cone)

end

@instance ThCategoryUnbiasedProducts{ACSet,ACSetTransformation}  [model::ACSetCategory] begin 

  limit(d::DiscreteDiagram) = pointwise_limit(model, d)

  universal(lim::AbsLimit, ::DiscreteDiagram, cone::Multispan) = 
    pointwise_universal(model, lim, cone)

end 


@instance ThCategoryWithEqualizers{ACSet,ACSetTransformation}  [model::ACSetCategory] begin 

  limit(d::ParallelMorphisms) = pointwise_limit(model, d)

  universal(lim::AbsLimit, ::ParallelMorphisms, cone::Multispan) = 
    pointwise_universal(model, lim, cone)
  
end 

@instance ThCategoryWithPullbacks{ACSet,ACSetTransformation}  [model::ACSetCategory] begin 

  limit(d::Multicospan) = pointwise_limit(model, d)

  universal(lim::AbsLimit, ::Multicospan, cone::Multispan) = 
    pointwise_universal(model, lim, cone)
  
end 

@instance ThCategoryWithBipartiteLimits{ACSet,ACSetTransformation}  [model::ACSetCategory] begin 

  limit(d::BipartiteFreeDiagram) = pointwise_limit(model, d)

  universal(lim::AbsLimit, ::BipartiteFreeDiagram, cone::Multispan) = 
    pointwise_universal(model, lim, cone)
end 

@instance ThCategoryWithLimits{ACSet,ACSetTransformation}  [model::ACSetCategory] begin 

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
    𝒟 = attr_cat(model, o)
    o => universal[𝒟](lim.limits[o], getvalue(upa[o]))
  end)
  ACSetTransformation(merge(comps, acomps), apex(cone), ob(lim); cat=model)
end

"""
Compute a limit in an ACSet category by pointwise limits for each object 
(in the entity category) and attrtype in the (in the attribute category).
"""
function pointwise_limit(model, d)
  Fd = FreeDiagram(d)
  𝒞 = entity_cat(model)
  upe, upa = unpack(model, Fd)
  limits_e = NamedTuple(map(collect(pairs(upe))) do (k, v)
    k => limit[𝒞](getvalue(v))
  end)
  limits_a = NamedTuple(map(collect(pairs(upa))) do (k, v)
    k => limit[attr_cat(model, k)](getvalue(v))
  end)
  Xs = cone_objects(d)
  πs_e = map(legs, limits_e)
  πs_a = map(legs, limits_a)
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
  S = acset_schema(C)
  type_assignment = map(attrtypes(S)) do at 
    e_set = getvalue(ob_map[attr_cat(C, at)](ob(attr_limits[at])))
    e_set isa EitherSet || error(
      "Expect underlying sets of attrtypes to be either, not $e_set")
    eltype(right(e_set))
  end

  # The type components need to be different for the apex
  ACS = typeof(constructor(C))
  Y = if isempty(attrtypes(S)); 
    ACS()
  else
    ACSUnionAll = Base.typename(ACS).wrapper
    ACSUnionAll{type_assignment...}()
  end

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
  for (f, c, d) in attrs(S)
    𝒟, 𝒫 = attr_cat(C, d), prof_cat(C, d)
    O, H = impl_type.(Ref(𝒟), Ref(ThCategory), [:Ob, :Hom])
    Yfs = map(zip(legs(entity_limits[c]), Xs)) do (π, X)
      ThHeteroMorphism.pre[𝒫](π, get_attr(C, X, f)
                ) |> interpret_heteromorphisms_as_codhoms
    end |> Vector{H}
    feet = Vector{O}(codom[𝒟].(Yfs))
    sp = Multispan{O, H, O}(Int, Yfs, feet)
    Yf = universal[𝒟](attr_limits[d], sp)
    for pᶜ in parts(Y, c)
      Y[pᶜ, f] = Yf(pᶜ)
    end
  end
  return Y
end

""" 
In our profunctor category 𝒞→Σᵢ𝒟ᵢ, when we have a pointwise limit and are trying
to compute an attribute heteromorphism h: a -> x

```
 lim(a)  -----> lim(x)
π₁↙ ↘π₂      Π₁↙  ↘Π₂
a₁   a₂      x₁   x₂ 
↓    ↓        ↑    ↑
↓    ↘------------↗  
↘-------------↑
      h₁
```

In order to get the heteromorphism lim(a)→lim(x) via the universal property of 
lim(x) as a product, we need to interpret the heteromorphisms πᵢ⋅hᵢ as morphisms 
in 𝒟 (because this is where the universal property of lim(x) is defined.)

It seems plausible we can expect this because the objects and morphisms of 𝒞 are 
generally finite things while things in 𝒟 are infinite.

We should eventually make this explicit in the interface for ACSetCategories.
This is an ad hoc solution originally designed for LooseACSet categories which 
are the only instance of limits of attributes supported in Catlab 0.16.
"""
function interpret_heteromorphisms_as_codhoms(f::FinDomFunction)
  SetFunction(f)
end 


end # module