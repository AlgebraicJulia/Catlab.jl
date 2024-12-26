module VarACSetCats
export VarACSetCat, abstract_attributes, var_reference

using StructEquality, MLStyle
using GATlab, ACSets
using ACSets.DenseACSets: attr_type

using .....BasicSets, ....SetCats
using ....Cats: ThCategoryExplicitSets, ThCategoryUnbiasedProducts
using ...CSets, ...ACSetTransformations
using ....SetCats: AbsVarFunction
import ..ACSetCats: coerce_component, coerce_attr_component_nothing
using ..PointwiseCats: AbsACSetCat
using .ThACSetCategory

"""
The category of VarACSets has objects which are ACSets with attributes valued in 
elements of some (fixed) Julia type or elements of a finite set.
"""
@struct_hash_equal struct VarACSetCat <: AbsACSetCat
  constructor::Any
  function VarACSetCat(x::ACSet)
    new(constructor(x))
  end
end

ACSets.acset_schema(c::VarACSetCat) = acset_schema(c.constructor())

@instance ThACSetCategory{SkelFinSet, InitialModel′, InitialModel′,
                          FinSetInt, FinFunction, FinSetInt, VarFunction, 
                          VarFunction,Symbol,ACSet,ACSetTransformation,
                          AbsSet, AbstractVector
                         } [model::VarACSetCat] begin

  constructor()::ACSet = model.constructor()

  function coerce(f::ACSetTransformation)
    X, Y, S = dom(f), codom(f), acset_schema(model)
    comps = Dict(map(ob(S)) do o
      o => coerce_component(o, get(components(f), o, nothing), 
                    FinSet(get_ob[model](X, o)), FinSet(get_ob[model](Y, o)))
    end )
    attr_comps = Dict(map(attrtypes(S)) do o
      o => coerce_attr_component_nothing(o, get(components(f), o , nothing))
    end)
    _ACSetTransformation(merge(comps,attr_comps), X, Y)
  end

  entity_cat() = SkelFinSet()

  attr_cat() = SkelFinSet()

  prof_cat() = VarFunctionHeteroMorphism()
  
  get_ob(x::ACSet,o::Symbol)::FinSetInt = FinSetInt(nparts(x, o))

  get_hom(x::ACSet,h::Symbol)::FinFunction = 
    FinFunction(x[h], FinSet(get_ob[model](x, codom(acset_schema(x), h))))

  get_op(::ACSet,::Symbol)::Union{} = error("Does not exist")

  function get_attr(x::ACSet,h::Symbol)::VarFunction 
    S, T = acset_schema(x), attr_type(x, h)
    v = map(x[h]) do elem 
      elem isa AttrVar ? getvalue(elem) : AttrVal{T}(elem)
    end
    VarFunction{T}(v, FinSet(get_ob[model](x, codom(S, h))))
  end

  get_attrtype(x::ACSet,o::Symbol)::FinSetInt = FinSetInt(nparts(x, o))

  get_set(x::FinSetInt) = FinSet(x)

  get_fn(x::FinFunction) = collect(x)

  get_attr_set(x::FinSetInt) = FinSet(x)

  get_attr_fn(x::AbsVarFunction{T}) where T = 
    FinDomFunction(map(dom[AttrC{T}()](x)) do v
      x(v) isa AttrVal ? getvalue(x(v)) : AttrVar(x(v))
    end, SetOb(UnionSet(SetOb(AttrVal), SetOb(T))))

end

coerce_attr_component_nothing(::Symbol, f::AbsVarFunction) = f



# Misc other methods
####################

"""
For any ACSet, X, a canonical map A→X where A has distinct variables for all
attributes valued in attrtypes present in `abstract` (by default: all attrtypes)
"""
function abstract_attributes(X::ACSet, abstract=nothing)
  S = acset_schema(X)
  abstract = isnothing(abstract) ? attrtypes(S) : abstract
  A = copy(X)
  comps = Dict{Any, Any}(map(abstract) do at
    rem_parts!(A, at, parts(A, at))
    comp = Union{AttrVar, attrtype_type(X, at)}[]
    for (f, d, _) in attrs(S; to=at)
      append!(comp, X[f])
      A[f] = AttrVar.(add_parts!(A, at, nparts(A, d)))
    end
    at => comp
  end)
  for o in ob(S) comps[o]=parts(X,o) end
  return ACSetTransformation(A,X; comps...)
end 

abstract_attributes(f::ACSetTransformation) = abstract_attributes(dom(f)) ⋅ f

"""
Find some part + attr that refers to an AttrVar. 
Throw error if none exists (i.e. `i` is a wandering variable).
"""
function var_reference(X::ACSet, at::Symbol, i::Int)
  S = acset_schema(X)
  for (f, c, _) in attrs(S; to=at)
    inc = incident(X, AttrVar(i), f)
    if !isempty(inc)
      return (f, c, first(inc))
    end
  end
  error("Wandering variable $at#$p")
end

end # module
