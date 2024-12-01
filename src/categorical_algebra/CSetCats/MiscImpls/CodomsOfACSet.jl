module CodomsOfACSet
export CodomOfACSet

using StructEquality
using ACSets, GATlab
using ACSets.DenseACSets: attrtype_type
import ACSets: acset_schema

using ....Cats: obtype, homtype
using ...ACSetTransformations: ACSetTransformation
using ..CSets: ACSetCategory, get_ob, get_hom, opcompose, attrid
using .ThCategory


"""
Every ACSet category implicitly defines a codomain category in which the 
ACSet is valued.
"""
@struct_hash_equal struct CodomOfACSet{O,H,AT,A} <: Model{Tuple{Union{O,AT},Union{H,A}}}
  val::ACSetCategory
  CodomOfACSet(i::ACSetCategory) = 
    new{obtype(i), homtype(i), attrtype_type(i),  attrtype(i)}(i)
end
 
GATlab.getvalue(c::CodomOfACSet) = c.val

acset_schema(c::CodomOfACSet) = acset_schema(getvalue(c))

@instance ThCategory{Union{O,AT},Union{H,A}} [model::CodomOfACSet{O,H,AT,A}]  where {O,H,AT,A} begin
  dom(f::Union{H,A})::Union{O,AT} = (f isa H ? dom : attrdom)(model, f)
  codom(f::Union{H,A})::Union{O,AT} = (f isa H ? codom : attrcodom)(model, f)

  function id(x::Union{O,AT})::Union{H,A}
    (x isa O ? id : attrid)(getvalue(model), x)
  end

  function compose(f::Union{H,A}, g::Union{H,A})::Union{H,A}
    (f isa H ? compose : opcompose)(getvalue(model), f, g)
  end
end 


end # module 
