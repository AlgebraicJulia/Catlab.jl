module ACSetCats
export ACSetCat, get_set, get_fn, get_attr_set, get_attr_fn

using StructEquality

using GATlab, ACSets
using ACSets.DenseACSets: attrtype_type, attr_type

import .....Theories: dom, codom
using .....BasicSets
using ....Cats, ....SetCats
using ...Heteromorphisms
using ...CSets, ...ACSetTransformations
import ..CSetCats: coerce_component
using ..PointwiseCats: AbsACSetCat

using .ThACSetCategory

# HeteroMorphisms 
#################

"""
Model of heteromorphisms where the domain and heteromorphisms are setfunctions 
but the codomain is discrete (only identity morphisms)
"""
@struct_hash_equal struct TrivialCodom end 

@instance ThHeteroMorphism{FinSetInt, Nothing, FinFunction, Nothing, AbsFinDomFunction
                          } [model::TrivialCodom] begin
  dom(h::AbsFinDomFunction)::FinSetInt = getvalue(dom(h))
  codom(h::AbsFinDomFunction)::Nothing = nothing
  pre(a::FinFunction, h::AbsFinDomFunction)::AbsFinDomFunction = compose[SetC()](a, h)
  post(a::AbsFinDomFunction, ::Nothing)::AbsFinDomFunction = a
end 

# ACSetCategory
###############

"""
The category of attributed C-sets and tight homomorphisms is isomorphic to a
slice category of C-Set, as explained in our paper "Categorical Data Structures
for Technical Computing". Colimits in this category thus reduce to colimits of
C-sets, by a standard result about slice categories. Limits are more complicated
and are currently not supported.
"""
@struct_hash_equal struct ACSetCat <: AbsACSetCat
  constructor::Any
  function ACSetCat(x::ACSet)
    new(constructor(x))
  end
end

ACSetCat(T::Type) = ACSetCat(T())
ACSets.acset_schema(x::ACSetCat) = acset_schema(x.constructor())
dom(c::ACSetCat, x) = dom(acset_schema(c), x)
codom(c::ACSetCat, x) = codom(acset_schema(c), x)

@instance ThACSetCategory{
    Ob = FinSetInt, Hom = FinFunction, 
    AttrType = Nothing, Op = Nothing, Attr = AbsFinDomFunction, 
    EntityCat = SkelFinSet, AttrCat = TerminalModel′, ProfCat = TrivialCodom
  } [model::ACSetCat] begin

  constructor()::ACSet = model.constructor()

  # Interpreting the data from the ACSet as living in some collage category
  entity_cat() = SkelFinSet()

  attr_cat(::Symbol) = TrivialCat()

  prof_cat(::Symbol) = TrivialCodom()

  # Interpret user-friendly ACSetTransformation data in an intuitive way

  coerce_hom(f::Any,d::FinSetInt,c::FinSetInt) = 
    coerce_component(f,FinSet(d),FinSet(c))

  coerce_op(::Any,::Nothing,::Nothing) = nothing

  # Interpret user-friendly ACSetTransformation data in an intuitive way

  get_ob(x::ACSet,o::Symbol)::FinSetInt = FinSetInt(nparts(x, o))

  function get_hom(x::ACSet,h::Symbol)::FinFunction 
    S = acset_schema(x)
    if h ∈ ob(S)
      FinFunction(FinSet(get_ob[model](x, h)))
    else 
      FinFunction(x[h], FinSet(get_ob[model](x, codom(model,h))))
    end
  end

  get_op(::ACSet,::Symbol)::Nothing = error("No ops in schemas")

  get_attr(x::ACSet,h::Symbol)::FinDomFunction = 
    FinDomFunction(x[h], SetOb(attr_type(x, h)))
  
  get_attrtype(::ACSet,::Symbol)::Nothing = nothing

  # Extracting Ob/Hom data from an ACSet data structure

  get_set(x::FinSetInt) = FinSet(x)

  get_fn(x::FinFunction, ::FinSetInt, ::FinSetInt)::AbsFinDomFunction = x
  
  get_attr_fn(f::AbsFinDomFunction, ::FinSetInt, ::Nothing)::AbsFinDomFunction = f
  get_op_fn(::Nothing, ::Nothing, ::Nothing)::AbsFinDomFunction = FinFunction([], FinSet(0))

  get_attr_set(::Nothing) = FinSet()

end

coerce_attr_component_nothing(::Symbol, ::Nothing) = nothing 

coerce_attr_component_nothing(o::Symbol, f::SetFunction) = 
  isempty(f) ? nothing : error("Bad $o component: $f")

coerce_attr_component_nothing(o::Symbol, f::Vector) = 
  isempty(f) ? nothing : error("Bad $o component: $f")

# """ The *default* category to interpret an ACSet in """
# ACSetCategory(x::ACSet) = ACSetCategory(ACSetCat(x))


end # module
