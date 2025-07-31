module MADACSetCats 
export MADACSetCat

using StructEquality, MLStyle
using GATlab, ACSets
using ACSets.DenseACSets: attrtype_type, attr_type

using .....BasicSets, ....SetCats
using ....Cats: ThCategoryExplicitSets, ThCategoryUnbiasedProducts, ConcreteCategory
using ...CSets, ...ACSetTransformations
using ...Heteromorphisms
using ..PointwiseCats: AbsACSetCat
using ..ACSetCats: TrivialCodom, RightTrivialCat

using .ThACSetCategory

"""
The category of C-Sets has objects which are dense ACSets with no attributes.
These are diagrams in the skeleton of FinSet.
"""
@struct_hash_equal struct MADACSetCat <: AbsACSetCat
  constructor::Any
  function MADACSetCat(x::ACSet{BitSetParts})
    new(constructor(x))
  end
end

MADACSetCat(s::Type) = MADACSetCat(s())

@instance ThACSetCategory{
    Ob = FinSet, Hom = FinFunction, 
    AttrType = Nothing, Op = Nothing, Attr = FinDomFunction,
  } [model::MADACSetCat] begin
 
  # Interpreting the data from the ACSet as living in some collage category

  entity_cat() = FinSetC()

  attr_cat(s::Symbol) = RightTrivialCat(
    attrtype_type(constructor[model](),s))

  prof_cat(::Symbol) = TrivialCodom()

  # An empty ACSet (useful for implementation details e.g. indexing)

  constructor()::ACSet = model.constructor()

  # Interpret user-friendly ACSetTransformation data in an intuitive way

  coerce_hom(f::Any, d::FinSet, c::FinSet) = 
    coerce_component(f,d,c)

  coerce_op(::Any,::Nothing,::Nothing) = nothing

  # Extracting Ob/Hom data from an ACSet data structure

  get_ob(x::ACSet, o::Symbol)::FinSet = FinSet(Set(parts(x, o)))

  function get_hom(x::ACSet, h::Symbol)::FinFunction
    S = acset_schema(x)
    if h ∈ ob(S)
      SetFunction(get_ob[model](x, h))
    else 
      v = Dict{Int,Int}([p=>x[p,h] for p in parts(x, dom(S, h))])
      FinFunction(v, get_ob[model](x, codom(S, h)))
    end
  end

  get_op(::ACSet, ::Symbol)::Union{} = error("No ops in schemas")

  function get_attr(x::ACSet, h::Symbol)
    v = Pair{Int,attr_type(x,h)}[p=>x[p,h] for p in parts(x, dom(model, h))]
    FinDomFunction(Dict(v), SetOb(attr_type(x, h)))
  end

  get_attrtype(::ACSet, ::Symbol)::Nothing = nothing

end

  
""" Check nat trans component dom/codom matches those of the ACSets """
function coerce_component(f::FinFunction, d::FinSet, cd::FinSet)
  dom(f) ≃ d || error("Domain error: got $(sort(collect(dom(f)))) not extensionally equiv to expected $(sort(collect(d)))")
  codom(f) ≃ cd || error("Codomain error: $(codom(f)) not extensionally equiv to $cd")
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


coerce_component(f::AbstractVector{Int}, d::FinSet, cd::FinSet) = 
  coerce_component(Dict(Iterators.filter(v->v[2]!=0, enumerate(f))), d, cd)

function coerce_component(::Nothing, d::FinSet, cd::FinSet)
  dic = Dict{eltype(d), eltype(cd)}(isempty(d) ? [] : [e=>only(cd) for e in d])
  coerce_component(dic, d, cd)
end

end # module
