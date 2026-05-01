module CSetCats 
export CSetCat, coerce_component

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
@struct_hash_equal struct CSetCat <: AbsACSetCat
  constructor::Any
  function CSetCat(x::ACSet{IntParts})
    s = acset_schema(x)
    isempty(s.attrtypes ∪ s.attrs) || error("Bad CSet schema")
    new(constructor(x))
  end
end

CSetCat(s::Type) = CSetCat(s())

@instance ThACSetCategory{
    Ob = FinSetInt, Hom = FinFunction, 
    AttrType = Union{}, Op = Union{}, Attr = Union{},
  } [model::CSetCat] begin
 
  # Interpreting the data from the ACSet as living in some collage category

  entity_cat() = SkelFinSet()

  attr_cat(::Symbol) = InitialModel

  prof_cat(::Symbol) = InitialModel

  # An empty ACSet (useful for implementation details e.g. indexing)

  constructor()::ACSet = model.constructor()

  # Interpret user-friendly ACSetTransformation data in an intuitive way

  coerce_hom(f::Any, d::FinSetInt, c::FinSetInt) = 
    coerce_component(f,FinSet(d),FinSet(c))

  # Extracting Ob/Hom data from an ACSet data structure

  get_ob(x::ACSet, o::Symbol)::FinSetInt = FinSetInt(nparts(x, o))

  function get_hom(x::ACSet, h::Symbol)::FinFunction
    S = acset_schema(x)
    if h ∈ ob(S)
      SetFunction(FinSet(get_ob[model](x, h)))
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
  dom(f) ≃ d || error("Domain error: Got $(dom(f)), expected $d")
  codom(f) ≃ cd || error("Codomain error: Got $(codom(f)), expected $cd")
  return f
end

""" Giving component as a Vector means assuming that domain is a FinSetInt """
function coerce_component(f::AbstractVector, d::FinSet, cd::FinSet)
  FinSet(length(f)) == d ||error("Domain error: $(FinSet(length(f))) ≠ $d")
  for (i, v) in enumerate(f) 
    v ∈ cd || error("Codomain error for dom element #$i: $v ∉ $cd")
  end
  return FinFunction(f, cd)
end

""" 
Not giving any data for a component means assuming it must be canonical, i.e. an 
empty domain or singleton codomain 
"""
function coerce_component(::Nothing, d::FinSet, cd::FinSet)
  if length(d) == 0
    FinFunction(getvalue(d) isa FinSetInt ? Int[] : Set{eltype(cd)}(), cd)
  elseif length(cd) == 1
    FinFunction(ConstantFunction(only(cd), d, cd))
  else 
    error("Missing component with dom $d and codom $cd")
  end
end

end # module
