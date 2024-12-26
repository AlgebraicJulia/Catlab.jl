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

"""
The category of ACSets (and *tight* transformations) has ...
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

@instance ThACSetCategory{SkelFinSet, TerminalModel′, TrivialCodom,
                          FinSetInt, FinFunction, Nothing, Nothing, FinDomFunction,     
                          Symbol, ACSet, ACSetTransformation,
                          AbsSet, AbstractVector
                         } [model::ACSetCat] begin

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

  attr_cat() = TrivialCat()

  prof_cat() = TrivialCodom()
  
  get_ob(x::ACSet,o::Symbol)::FinSetInt = FinSetInt(nparts(x, o))

  get_hom(x::ACSet,h::Symbol)::FinFunction = 
    FinFunction(x[h], FinSet(get_ob[model](x, codom(model,h))))

  get_op(::ACSet,::Symbol)::Nothing = error("No ops in schemas")

  get_attr(x::ACSet,h::Symbol)::SetFunction = 
    FinDomFunction(x[h], SetOb(attr_type(x, h)))
  
  get_attrtype(::ACSet,::Symbol)::Nothing = nothing

  get_set(x::FinSetInt) = FinSet(x)

  get_fn(x::FinFunction) = collect(x)
  
  get_attr_fn(f::FinDomFunction) = f

  get_attr_set(::Nothing) = FinSet()                            

end

coerce_attr_component_nothing(::Symbol, ::Nothing) = nothing 

coerce_attr_component_nothing(o::Symbol, f::SetFunction) = f


# """ The *default* category to interpret an ACSet in """
# ACSetCategory(x::ACSet) = ACSetCategory(ACSetCat(x))


end # module
