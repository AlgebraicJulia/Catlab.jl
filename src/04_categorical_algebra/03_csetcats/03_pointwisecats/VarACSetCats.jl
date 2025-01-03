module VarACSetCats
export VarACSetCat, abstract_attributes, var_reference

using StructEquality, MLStyle
using GATlab, ACSets
using ACSets.DenseACSets: attr_type, attrtype_type

using .....BasicSets, ....SetCats
using ....Cats: ThCategoryExplicitSets, ThCategoryUnbiasedProducts
using ...CSets, ...ACSetTransformations
using ....SetCats: AbsVarFunction
import ..ACSetCats: coerce_component
using ..PointwiseCats: AbsACSetCat
using .ThACSetCategory

"""
The category of VarACSets has objects which are ACSets with attributes valued in 
elements of some (fixed) Julia type or elements of a finite set.
"""
@struct_hash_equal struct VarACSetCat <: AbsACSetCat
  constructor::Any
  VarACSetCat(x::ACSet) = new(constructor(x))
end

ACSets.acset_schema(c::VarACSetCat) = acset_schema(c.constructor())

@instance ThACSetCategory{SkelFinSet, InitialModel′, InitialModel′,
                          FinSetInt, FinFunction, FinSetInt, VarFunction, 
                          VarFunction,Symbol, Any, ACSet,ACSetTransformation,
                          AbsSet, AbstractVector
                         } [model::VarACSetCat] begin

  constructor()::ACSet = model.constructor()

  coerce_ob(f::Any,d::FinSetInt,c::FinSetInt) = 
    coerce_component(f,FinSet(d),FinSet(c))

  coerce_attr(f::Any,T::Any,d::FinSetInt,c::FinSetInt) = 
    coerce_attr_varfun(f, T, FinSet(d), FinSet(c))

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

function coerce_attr_varfun(f::AbsVarFunction{T′}, T::Type, 
                            d::FinSet, cd::FinSet)  where {T′}
  T′ <: T || error("Bad VarFunction type: $(T′) ⊀ $(T)  ")
  dom(f) == d || error("bad $f $(dom(f))≠$d")
  codom(f) == cd || error("bad $f $(codom(f))≠$cd")
  f
end

function coerce_attr_varfun(::Nothing, T::Type, d::FinSet, cd::FinSet) 
  isempty(d) || error("Bad: nonempty domain $d")
  return VarFunction{T}([], cd)
end

""" Assume this is a function purely on the FinSet component """
function coerce_attr_varfun(f::Fin_FinDom, T::Type, d::FinSet, cd::FinSet)
  dom(f) == d || error("Bad: mismatched dom $d ≠ $(dom(f))")
  codom(f) == cd || error("Bad: mismatched dom $cd ≠ $(codom(f))")
  inject(f, T)
end

function coerce_attr_varfun(f::Vector, T::Type, d::FinSet, cd::FinSet) 
  length(f) == length(d) && getvalue(d) isa FinSetInt ||  error(
    "Bad domain $d for $f")
  VarFunction{T}(map(f) do v 
    if v isa AttrVar
      getvalue(v) ∈ cd || error("Bad value $v for codom $cd")
      getvalue(v)
    elseif v isa T 
      AttrVal{T}(v)
    else 
      error("Bad::$T value: $v :: $(typeof(v))")
    end
  end, cd)

end


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
