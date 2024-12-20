module CSetCats 
export CSetCat, coerce_component

using StructEquality, MLStyle
using GATlab, ACSets

using .....BasicSets, ....SetCats
using ....Cats: ThCategoryExplicitSets, ThCategoryUnbiasedProducts
using ...CSets, ...ACSetTransformations
using ..PointwiseCats: AbsACSetCat

using .ThACSetCategory

# Instances of ACSet Categories
################################ 

# Because Julia disallows Union{} in Tuples, the type of Attrs of a CSetCat is 
# unit type, even though it ought be the empty type.
"""
The category of C-Sets has objects which are ACSets with no attributes. The 
ACSets can have arbitrary FinSets (thus encompass DenseACSets and MarkAsDeleted
ACSets, or possibly ACSets with sets that are non-integer elements). For the 
subcategory of `CSetCat` which only has DenseACSets with integer elements, see
`CSkelFinSet`.
"""
@struct_hash_equal struct CSetCat <: AbsACSetCat{
    SkelFinSet, Any, Any, FinSet, FinFunction, Union{}, Union{}, Union{}}
  constructor::Any
  function CSetCat(x::ACSet)
    s = acset_schema(x)
    isempty(s.attrtypes ∪ s.attrs) || error("Bad CSet schema")
    new(constructor(x))
  end
end

CSetCat(s::Type) = CSetCat(s())
ACSets.acset_schema(c::CSetCat) = acset_schema(c.constructor)

@instance ThACSetCategory{SkelFinSet, InitialModel, InitialModel,
                          FinSet, FinFunction, Union{}, Union{}, Union{},
                          Symbol,ACSet,ACSetTransformation
                         } [model::CSetCat] begin
  constructor()::ACSet = model.constructor()

  function coerce(f::ACSetTransformation)
    X, Y, = dom(f), codom(f)
    comps = Dict(map(ob(acset_schema(X))) do o
      o => coerce_component(o, get(components(f), o, nothing), 
                       FinSet(get_ob[model](X, o)), FinSet(get_ob[model](Y, o)))
    end )
    _ACSetTransformation(comps, X, Y)
  end

  entity_cat() = SkelFinSet()

  attr_cat() = InitialModel(ThCategoryUnbiasedProducts)

  prof_cat() = InitialModel(ThProfunctor)
  
  get_ob(x::ACSet,o::Symbol)::FinSetInt = FinSetInt(nparts(x, o))

  get_hom(x::ACSet,h::Symbol)::FinFunction = 
    FinFunction(x[h], FinSet(get_ob[model](x, codom(acset_schema(x), h))))

  get_op(::ACSet,::Symbol)::Union{} = error()
  get_attr(::ACSet,::Symbol)::Union{} = error()
  get_attrtype(::ACSet,::Symbol)::Union{} = error()

end

  
""" Check nat trans component dom/codom matches those of the ACSets """
function coerce_component(o::Symbol, f::FinFunction, d::FinSet, cd::FinSet)
  dom(f) == d || error("Domain error in $o: $(dom(f)) != $d")
  codom(f) == cd || error("Domain error in $o: $(codom(f)) != $cd")
  return f
end

""" Giving component as a Vector means assuming that domain is a FinSetInt """
function coerce_component(o::Symbol, f::AbstractVector, d::FinSet, cd::FinSet)
  FinSet(length(f)) == d ||error("Domain error in $o: $(FinSet(length(f))) ≠ $d")
  for (i, v) in enumerate(f) 
    v ∈ cd || error("Codomain error in $o for dom element #$i: $v ∉ $cd")
  end
  return FinFunction(f, cd)
end

""" 
Not giving any data for a component means assuming it must be canonical, i.e. an 
empty domain or singleton codomain 
"""
function coerce_component(o::Symbol, ::Nothing, d::FinSet, cd::FinSet)
  if nX == 0
    FinFunction([], cd)
  elseif nparts(Y,o) == 1
    FinFunction(ConstantFunction(only(parts(Y, o)), d, cd))
  else 
    error("Missing component $o")
  end
end

end # module
