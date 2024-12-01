module CatsOfACSet
export CatOfACSet

using StructEquality
using ACSets, GATlab
import ACSets: acset_schema

# using ....Cats.Categories: CatImpl, ThCategoryExplicitSets
using ...ACSetTransformations: ACSetTransformation
using ..CSets: ACSetCategory, get_ob, get_hom
using .ThCategory

@struct_hash_equal struct CatOfACSet <: Model{Tuple{ACSet, ACSetTransformation}}
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
    ecomps = Dict(o => id(M, get_ob(M, x, o)) for o in ob(S))
    acomps = Dict(o => attr_id(M, get_attrtype(M, x, o)) for o in attrtypes(S))
    ACSetTransformation(merge(ecomps, acomps), x, x)
  end

  function compose(f::ACSetTransformation, g::ACSetTransformation)
    M, S = getvalue(model), acset_schema(model)
    ecomps = Dict(o => compose(M, f[o], g[o]) for o in ob(S))
    acomps = Dict(o => opcompose(M, f[o], g[o]) for o in attrtypes(S))
    ACSetTransformation(merge(ecomps, acomps), f.dom, g.codom)
  end
end 


end # module 
