module CatsOfACSet
export CatOfACSet

using StructEquality
using ACSets, GATlab
import ACSets: acset_schema

using ....Cats: Category
using ...ACSetTransformations: ACSetTransformation
using ...CSets
using .ThCategory

@struct_hash_equal struct CatOfACSet
  val::ACSetCategory
end
 
GATlab.getvalue(c::CatOfACSet) = c.val

acset_schema(c::CatOfACSet) = acset_schema(getvalue(c))

@instance ThCategory{ACSet, ACSetTransformation} [model::CatOfACSet] begin
  Hom(f::ACSetTransformation, dom::ACSet, cod::ACSet) = coerce(getvalue(model), f, dom, cod)
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
    M, S = getvalue(model), acset_schema(model)
    𝒞, 𝒟 = Category(entity_cat(M)), Category(attr_cat(M))

    ecomps = Dict(o => compose(𝒞, f[o], g[o]) for o in ob(S))
    acomps = Dict(o => opcompose(𝒟, f[o], g[o]) for o in attrtypes(S))
    ACSetTransformation(merge(ecomps, acomps), f.dom, g.codom, M)
  end
end 


end # module 
