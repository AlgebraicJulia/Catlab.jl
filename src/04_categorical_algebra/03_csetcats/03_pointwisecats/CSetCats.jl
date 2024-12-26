module CSetCats 
export CSetCat, coerce_component

using StructEquality, MLStyle
using GATlab, ACSets

using .....BasicSets, ....SetCats
using ....Cats: ThCategoryExplicitSets, ThCategoryUnbiasedProducts
using ...CSets, ...ACSetTransformations
using ..PointwiseCats: AbsACSetCat

using .ThACSetCategory

"""
The category of C-Sets has objects which are ACSets with no attributes.
These are diagrams in the skeleton of FinSet.
"""
@struct_hash_equal struct CSetCat <: AbsACSetCat
  constructor::Any
  function CSetCat(x::ACSet)
    s = acset_schema(x)
    isempty(s.attrtypes ∪ s.attrs) || error("Bad CSet schema")
    new(constructor(x))
  end
end

CSetCat(s::Type) = CSetCat(s())
ACSets.acset_schema(c::CSetCat) = acset_schema(c.constructor)

@instance ThACSetCategory{SkelFinSet, InitialModel′, InitialModel′,
                          FinSetInt, FinFunction, Union{}, Union{}, Union{},
                          Symbol,ACSet,ACSetTransformation,
                          AbsSet, AbstractVector
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

  attr_cat() = InitialModel

  prof_cat() = InitialModel
  
  get_ob(x::ACSet,o::Symbol)::FinSetInt = FinSetInt(nparts(x, o))

  get_hom(x::ACSet,h::Symbol)::FinFunction = 
    FinFunction(x[h], FinSet(get_ob[model](x, codom(acset_schema(x), h))))

  get_op(::ACSet,::Symbol)::Union{} = error()

  get_attr(::ACSet,::Symbol)::Union{} = error()

  get_attrtype(::ACSet,::Symbol)::Union{} = error()

  get_set(x::FinSetInt) = FinSet(x)

  get_fn(x::FinFunction) = collect(x)

end

  
""" Check nat trans component dom/codom matches those of the ACSets """
function coerce_component(o::Symbol, f::SetFunction, d::FinSet, cd::FinSet)
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
  if length(d) == 0
    FinFunction(getvalue(d) isa FinSetInt ? Int[] : Set{eltype(cd)}(), cd)
  elseif nparts(Y,o) == 1
    FinFunction(ConstantFunction(only(parts(Y, o)), d, cd))
  else 
    error("Missing component $o")
  end
end

end # module
