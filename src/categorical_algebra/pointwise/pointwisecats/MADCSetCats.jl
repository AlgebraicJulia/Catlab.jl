module MADCSetCats 
export MADCSetCat

using StructEquality, MLStyle
using GATlab, ACSets

using .....BasicSets, ....SetCats
using ....Cats: ThCategoryExplicitSets, ThCategoryUnbiasedProducts, ConcreteCategory
using ...CSets, ...ACSetTransformations
using ..PointwiseCats: AbsACSetCat

using .ThACSetCategory

"""
The category of C-Sets has objects which are dense ACSets with no attributes.
These are diagrams in the skeleton of FinSet.
"""
@struct_hash_equal struct MADCSetCat <: AbsACSetCat
  constructor::Any
  function MADCSetCat(x::ACSet{BitSetParts})
    s = acset_schema(x)
    isempty(s.attrtypes ∪ s.attrs) || error("Bad CSet schema")
    new(constructor(x))
  end
end

MADCSetCat(s::Type) = MADCSetCat(s())

@instance ThACSetCategory{
    Ob = FinSet, Hom = FinFunction, 
    AttrType = Union{}, Op = Union{}, Attr = Union{},
  } [model::MADCSetCat] begin
 
  # Interpreting the data from the ACSet as living in some collage category

  entity_cat() = FinSetC()

  attr_cat(::Symbol) = InitialModel

  prof_cat(::Symbol) = InitialModel

  # An empty ACSet (useful for implementation details e.g. indexing)

  constructor()::ACSet = model.constructor()

  # Interpret user-friendly ACSetTransformation data in an intuitive way

  coerce_hom(f::Any, d::FinSet, c::FinSet) = 
    coerce_component(f,d,c)

  # Extracting Ob/Hom data from an ACSet data structure

  get_ob(x::ACSet, o::Symbol)::FinSet = FinSet(Set(parts(x, o)))

  function get_hom(x::ACSet, h::Symbol)::FinFunction
    S = acset_schema(x)
    if h ∈ ob(S)
      SetFunction(get_ob[model](x, h))
    else 
      FinFunction(x[h], FinSet(get_ob[model](x, codom(S, h))))
    end
  end

  get_op(::ACSet, ::Symbol)::Union{} = error()

  get_attr(::ACSet, ::Symbol)::Union{} = error()

  get_attrtype(::ACSet, ::Symbol)::Union{} = error()

end

  
""" Check nat trans component dom/codom matches those of the ACSets """
function coerce_component(f::FinFunction, d::FinSet, cd::FinSet)
  dom(f) ≃ d || error("Domain error: $(dom(f)) != $d")
  codom(f) ≃ cd || error("Codomain error: $(codom(f)) != $cd")
  return f
end

""" Giving component as a Dict means assuming that domain is a FinSetHash """
function coerce_component(f::Dict{Int,Int}, d::FinSet, cd::FinSet)
  d′ = FinSet(Set(keys(f)))
  d′ == d ||error("Domain error: $d′ ≠ $d")
  for (i, v) in collect(f)
    v ∈ cd || error("Codomain error for dom element #$i: $v ∉ $cd")
  end
  return FinFunction(f, cd)
end

coerce_component(f::Nothing, d::FinSet, cd::FinSet) = coerce_component(Int[], d, cd)


coerce_component(f::AbstractVector{Int}, d::FinSet, cd::FinSet) = 
  coerce_component(Dict(Iterators.filter(v->v[2]!=0, enumerate(f))), d, cd)

end # module
