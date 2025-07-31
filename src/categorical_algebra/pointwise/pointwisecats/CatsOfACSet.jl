module CatsOfACSet

using StructEquality
using ACSets, GATlab
import ACSets: acset_schema
using ACSets.DenseACSets: attrtype_type

using .....BasicSets: SetOb, is_monic, is_epic
using ....Cats: Category, ThCategoryExplicitSets, dom, codom, compose, id, 
                ThCategory, ThCategoryWithMonicsEpics
using ...ACSetTransformations: ACSetTransformation
using ...CSets


@instance ThCategory{ACSet, ACSetTransformation} [model::ACSetCategory] begin

  Hom(f::ACSetTransformation, dom::ACSet, cod::ACSet) = 
    coerce(getvalue(model), f, dom, cod)

  dom(f::ACSetTransformation) = f.dom

  codom(f::ACSetTransformation) = f.codom

  function id(x::ACSet) 
    M, S = model, acset_schema(model)
    𝒞, 𝒟 = Category(entity_cat(M)), t->Category(attr_cat(M,t))
    ecomps = Dict(o => id(𝒞, get_ob(M, x, o)) for o in ob(S))
    acomps = Dict(o => id(𝒟(o), get_attrtype(M, x, o)) for o in attrtypes(S))
    ACSetTransformation(merge(ecomps, acomps), x, x; cat=M)
  end

  function compose(f::ACSetTransformation, g::ACSetTransformation)
    S = acset_schema(model)
    f, g = coerce(f; cat=model), coerce(g; cat=model) # we shouldn't have to do this
    𝒞, 𝒟 = Category(entity_cat(model)), t->Category(attr_cat(model,t))
    ecomps = Dict(o => compose(𝒞, f[o], g[o]) for o in ob(S))
    acomps = Dict(o => compose(𝒟(o), f[o], g[o]) for o in attrtypes(S))
    ACSetTransformation(merge(ecomps, acomps), f.dom, g.codom; cat=model)
  end

end 

@instance ThCategoryExplicitSets{ACSet, ACSetTransformation
                                } [model::ACSetCategory] begin
                                
  ob_set() = SetOb(ACSet)

  hom_set() = SetOb(ACSetTransformation)

end

@instance ThCategoryWithMonicsEpics{ACSet, ACSetTransformation} [model::ACSetCategory] begin

  function is_monic(α::ACSetTransformation) 
    S, 𝒞 = acset_schema(model), entity_cat(model)
    all(o->is_monic[𝒞](α[o]), ob(S)) || return false
    for k in attrtypes(S)
      𝒞 = attr_cat(model, k)
      is_monic[𝒞](α[k]) || return false
    end
    return true 
  end

  function is_epic(α::ACSetTransformation)
    S, 𝒞 = acset_schema(model), entity_cat(model)
    all(o->is_epic[𝒞](α[o]), ob(S)) || return false
    for k in attrtypes(S)
      𝒞 = attr_cat(model, k)
      is_epic[𝒞](α[k]) || return false
    end
    return true 
  end 
end



end # module 
