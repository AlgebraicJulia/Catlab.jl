module VarACSetCats
export VarACSetCat, abstract_attributes, var_reference

using StructEquality, MLStyle
using GATlab, ACSets
using ACSets.DenseACSets: attr_type
import ACSets.DenseACSets: attrtype_type

using .....Theories: compose
using .....BasicSets, ....SetCats
using ...CSets, ...ACSetTransformations
using ..PointwiseCats: AbsACSetCat
import ..ACSetCats: coerce_component
using .ThACSetCategory

# Heteromorphisms 
#################


""" 
HeteroMorphism composition appropriate for C ⇥ D where C isa FinSet-like 
category and D is a category with Kleisli composition.
"""
@struct_hash_equal struct VarProf{T} end 

@instance ThHeteroMorphism{DomOb=FinSetInt,CodOb=FinSetInt,DomHom=FinFunction, CodHom=FinDomFunction, Het=FinDomFunction
                          } [model::VarProf{T}] where T begin

  dom(g::FinDomFunction) = dom[SkelKleisli(T)](g)
  
  codom(g::FinDomFunction) = codom[SkelKleisli(T)](g)

  pre(f::FinFunction, g::FinDomFunction) = precompose(g, f)

  post(f::FinDomFunction, g::FinDomFunction) = compose[SkelKleisli(T)](f, g)

end 

# ACSetCategory
###############
"""
The category of VarACSets has objects which are ACSets with attributes valued in 
elements of some (fixed) Julia type or elements of a finite set.
"""
@struct_hash_equal struct VarACSetCat <: AbsACSetCat
  constructor::Any
  VarACSetCat(x::ACSet) = new(constructor(x))
end

ACSets.acset_schema(c::VarACSetCat) = acset_schema(c.constructor())
attrtype_type(model::VarACSetCat, T::Symbol) = attrtype_type(model.constructor(), T)

@instance ThACSetCategory{
    Ob = FinSetInt, Hom = FinFunction, 
    AttrType = FinSetInt, Op = FinDomFunction, Attr = FinDomFunction, 
    EntityCat = SkelFinSet, AttrCat = SkelKleisli, ProfCat=VarProf
  } [model::VarACSetCat] begin

  constructor()::ACSet = model.constructor()

  # Interpreting the data from the ACSet as living in some collage category
  entity_cat() = SkelFinSet()

  attr_cat(T::Symbol) = SkelKleisli(attrtype_type(model, T)) 

  prof_cat(T::Symbol) = VarProf{attrtype_type(model, T)}()

  # Interpret user-friendly ACSetTransformation data in an intuitive way

  coerce_hom(f::Any,d::FinSetInt,c::FinSetInt) = 
    coerce_component(f,FinSet(d),FinSet(c))

  function coerce_op(f::Any,d::FinSetInt,c::FinSetInt; context)
    coerce_attr_varfun(f, context[:t], FinSet(d), FinSet(c))
  end

  # Extracting Ob/Hom data from an ACSet data structure

  get_ob(x::ACSet,o::Symbol)::FinSetInt = FinSetInt(nparts(x, o))

  get_hom(x::ACSet,h::Symbol)::FinFunction = 
    FinFunction(x[h], FinSet(get_ob[model](x, codom(acset_schema(x), h))))

  get_op(::ACSet,::Symbol)::Union{} = error("Does not exist")

  function get_attr(x::ACSet,h::Symbol)::FinDomFunction 
    S, T = acset_schema(x), attr_type(x, h)
    v = map(x[h]) do elem 
      elem isa AttrVar ? Left(getvalue(elem)) : Right(elem)
    end
    FinDomFunction(v, either(SetOb(FinSet(nparts(x, codom(S, h)))), SetOb(T)))
  end

  get_attrtype(x::ACSet,o::Symbol)::FinSetInt = FinSetInt(nparts(x, o))

  # Recovering ACSet data (FinSets and FinDomFunctions) back from Ob/Hom types

  get_set(x::FinSetInt)::FinSet = FinSet(x)

  get_fn(x::FinFunction, ::FinSetInt, ::FinSetInt)::FinDomFunction = FinDomFunction(x)

  get_attr_set(x::FinSetInt)::FinSet = FinSet(x)

  get_op_fn(x::FinDomFunction, ::FinSetInt, ::FinSetInt)::FinDomFunction = x

  get_attr_fn(x::FinDomFunction, ::FinSetInt, ::FinSetInt)::FinDomFunction = 
    FinDomFunction(map(dom(x)) do v
      fx = getvalue(x(v))
      x(v) isa Right ? fx : AttrVar(fx)
    end, SetOb(Any)) # KBTODO fix the codomain
end

function coerce_attr_varfun(f::SetFunction, T::Type, 
                            d::FinSet, cd::FinSet)
  T′ <: T || error("Bad VarFunction type: $(T′) ⊀ $(T)  ")
  dom(f) == d || error("bad $f $(dom(f))≠$d")
  codom(f) == cd || error("bad $f $(codom(f))≠$cd")
  f
end

function coerce_attr_varfun(::Nothing, T::Type, d::FinSet, cd::FinSet) 
  isempty(d) || error("Bad: nonempty domain $d")
  return FinDomFunction([], either(SetOb(cd),SetOb(T)))
end

"""  """
function coerce_attr_varfun(f::FinDomFunction, T::Type, d::FinSet, cd::FinSet)
  sort(collect(dom(f))) == sort(collect(d)) || error("Bad: mismatched dom $d ≠ $(dom(f))")
  # first we optimistically assume that we already have a VarFunction
  codom(f) == either(SetOb(cd), SetOb(T)) && return f
  # otherwise Assume this is a function purely on the FinSet component
  codom(f) == cd || error("Bad: mismatched dom $cd ≠ $(codom(f))")
  pure(f, T)
end

function coerce_attr_varfun(f::AbstractVector, T::Type, d::FinSet, cd::FinSet) 
  length(f) == length(d) && getvalue(d) isa FinSetInt ||  error(
    "Bad domain $d for $f")
  FinDomFunction(map(f) do v 
    if v isa AttrVar
      getvalue(v) ∈ cd || error("Bad value $v for codom $cd")
      Left(getvalue(v))
    elseif v isa T 
      Right(v)
    else 
      error("Bad::$T value: $v :: $(typeof(v))")
    end
  end, either(SetOb(cd), SetOb(T)))

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
