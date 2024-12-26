module CatsOfACSet

using StructEquality
using ACSets, GATlab
import ACSets: acset_schema

using .....BasicSets: AbsSet, SetOb
using ....Cats: Category, ThCategoryExplicitSets
using ...ACSetTransformations: ACSetTransformation
using ...CSets
using .ThCategory


@instance ThCategory{ACSet, ACSetTransformation} [model::ACSetCategory] begin

  Hom(f::ACSetTransformation, dom::ACSet, cod::ACSet) = 
    coerce(getvalue(model), f, dom, cod)

  dom(f::ACSetTransformation) = f.dom

  codom(f::ACSetTransformation) = f.codom

  function id(x::ACSet) 
    M, S = getvalue(model), acset_schema(model)
    𝒞, 𝒟 = Category(entity_cat(M)), Category(attr_cat(M))
    ecomps = Dict(o => id(𝒞, get_ob(M, x, o)) for o in ob(S))
    acomps = Dict(o => id(𝒟, get_attrtype(M, x, o)) for o in attrtypes(S))
    ACSetTransformation(merge(ecomps, acomps), x, x, M)
  end

  function compose(f::ACSetTransformation, g::ACSetTransformation)
    S = acset_schema(model)
    𝒞, 𝒟 = Category(entity_cat(model)), Category(attr_cat(model))

    ecomps = Dict(o => compose(𝒞, f[o], g[o]) for o in ob(S))
    acomps = Dict(o => opcompose(𝒟, f[o], g[o]) for o in attrtypes(S))
    ACSetTransformation(merge(ecomps, acomps), f.dom, g.codom, model)
  end

end 

@instance ThCategoryExplicitSets{ACSet, ACSetTransformation, AbsSet
                                } [model::ACSetCategory] begin
                                
  ob_set() = SetOb(ACSet)

  hom_set() = SetOb(ACSetTransformation)

end

end # module 
