module ACSetCats
export ACSetCat

using StructEquality

using GATlab, ACSets
using ACSets.DenseACSets: attrtype_type, attr_type

using .....BasicSets
using ....SetCats: AttrVal, VarFunction
using ....Cats: Category, TypeCat
import ....Cats: FinDomFunctor
using ..CSets: ACSetCategoryImpl, ThACSetCategory
using ..ACSetFunctors: ACSetFunctor
using ..ACSetTransformations: ACSetTransformation, _ACSetTransformation, components
using ..CSetCats: coerce_component

using .ThACSetCategory

"""
The category of ACSets (and *tight* transformations) has ...
"""
@struct_hash_equal struct ACSetCat{S} <: ACSetCategoryImpl{FinSet,FinFunction,Type,Nothing}
  constructor::Any
  function ACSetCat(x::ACSet)
    new{TypeLevelBasicSchema(acset_schema(x))}(constructor(x))
  end
end

ACSetCat(T::Type) = ACSetCat(T())


@instance ThACSetCategory{FinSet, FinFunction, Type, Nothing, FinDomFunction,     
                          Symbol, ACSet, ACSetTransformation
                         } [model::ACSetCat{S}] where S begin

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

  get_ob(x::ACSet,o::Symbol)::FinSet = FinSet(nparts(x, o))

  get_hom(x::ACSet,h::Symbol,a::FinSet,b::FinSet)::FinFunction = 
    FinFunction(x[h], b)

  get_attrtype(x::ACSet,a::Symbol)::Type = attrtype_type(x, a)

  get_attr(x::ACSet,f::Symbol,a::FinSet,b::Type)::FinDomFunction =
    FinDomFunction(AttrVal{attr_type(x,f)}.(x[f]), SetOb(b))

  attr_precompose(f::FinFunction,g::FinDomFunction)::FinDomFunction = 
    compose[SetC()](f,g)

  attr_postcompose(f::FinDomFunction,g::Nothing)::FinDomFunction = f

  opcompose(f::Nothing,g::Nothing)::Nothing = nothing

  id(f::FinSet)::FinFunction = FinFunction(f)

  attrid(f::Type)::Nothing = id[SetC()](SetOb(f))

  compose(f::FinFunction, g::FinFunction)::FinFunction = 
    ThCategory.compose[SetC()](f,g)

end

coerce_attr_component_nothing(::Symbol, ::Nothing) = nothing 

coerce_attr_component_nothing(o::Symbol, f::VarFunction) = 
  length(dom(f)) == 0 ? nothing : error("Invalid varfunction for $o: $f")


end # module
