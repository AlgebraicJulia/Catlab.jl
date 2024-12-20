module ACSetCats
export ACSetCat

using StructEquality

using GATlab, ACSets
using ACSets.DenseACSets: attrtype_type, attr_type

using .....BasicSets
using ....SetCats
using ...CSets, ...ACSetTransformations
using ..CSetCats: coerce_component
using ..PointwiseCats: AbsACSetCat

using .ThACSetCategory

"""
The category of ACSets (and *tight* transformations) has ...
"""
@struct_hash_equal struct ACSetCat <: AbsACSetCat{
    SkelFinSet, Any, Any,FinSetInt, FinFunction, Type, Union{}, FinDomFunction}
  constructor::Any
  function ACSetCat(x::ACSet)
    new(constructor(x))
  end
end

ACSetCat(T::Type) = ACSetCat(T())


@instance ThACSetCategory{SkelFinSet, Any, Any,
                          FinSetInt, FinFunction, Type, Union{}, FinDomFunction,     
                          Symbol, ACSet, ACSetTransformation
                         } [model::ACSetCat] begin

  constructor()::ACSet = model.constructor()

  function coerce(f::ACSetTransformation)
    X, Y = dom(f), codom(f)
    comps = Dict(map(ob(S)) do o
      o => coerce_component(o, get(components(f), o, nothing), 
                            get_ob[model](X, o), get_ob[model](Y, o))
    end )
    attr_comps = Dict(map(attrtypes(S)) do o
      o => coerce_attr_component_nothing(o, get(components(f), o , nothing))
    end)
    _ACSetTransformation(merge(comps,attr_comps), X, Y)
  end
  entity_cat() = SkelFinSet()

  attr_cat() = initial_instance(ThCategory)

  prof_cat() = initial_instance(ThProfunctor)
  
  get_ob(x::ACSet,o::Symbol)::FinSetInt = FinSetInt(nparts(x, o))

  get_hom(x::ACSet,h::Symbol)::FinFunction = 
    FinFunction(x[h], b)

  get_op(::ACSet,::Symbol)::Union{} = error()
  get_attr(x::ACSet,h::Symbol)::Union{} = FinFunction(x[h], b)
  get_attrtype(x::ACSet,b::Symbol)::Union{} = attrtype_type(x, b)

end

coerce_attr_component_nothing(::Symbol, ::Nothing) = nothing 

coerce_attr_component_nothing(o::Symbol, f::VarFunction) = 
  length(dom(f)) == 0 ? nothing : error("Invalid varfunction for $o: $f")


# """ The *default* category to interpret an ACSet in """
# ACSetCategory(x::ACSet) = ACSetCategory(ACSetCat(x))


end # module
