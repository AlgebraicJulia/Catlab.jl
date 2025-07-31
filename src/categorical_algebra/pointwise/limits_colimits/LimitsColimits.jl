export unpack, pack_components

using ACSets, GATlab
using ACSets.DenseACSets: attrtype_type

import ....Theories: ob
using ....BasicSets
using ...Cats, ...SetCats
import ...Cats: cone, cocone
using ..ACSetTransformations, ..CSets
using ..ACSetCats

####################
# Helper functions #
####################

""" 
Unpack a FreeDiagram{ACSet,ACSetTransformation} 
into a namedtuple of free diagrams, one for each ob/attrtype 
"""
function unpack(c::ACSetCategory, d::FreeDiagram)
  S = acset_schema(c)
  𝒞 = entity_cat(c) 
  O, H = impl_type.([𝒞,𝒞], Ref(ThCategory), [:Ob,:Hom])
  ents =NamedTuple(Dict(map(ob(S)) do o
    o => fmap(d, x->get_ob(c, x, o), x->coerce_hom(c, x, o), O, H)
  end))
  ats = NamedTuple(Dict(map(attrtype(S)) do o 
    𝒟 = attr_cat(c, o)
    T, P = impl_type.([𝒟,𝒟], Ref(ThCategory), [:Ob,:Hom])
    o => fmap(d, x -> get_attrtype(c, x, o), 
                 x -> coerce_op(c, x, o), 
                 T, P)
  end))
  ents => ats
end

""" Named tuple of vectors of FinFunctions → vector of C-set transformations.
"""
function pack_components(cat::ACSetCategory, fs::NamedTuple{names}, doms, codoms) where names
  components = map(1:length(doms)) do i 
    NamedTuple{names}(fs[n][i] for n in names)
  end
  # components = map((x...) -> NamedTuple{names}(x), fs...) causes error for empty tuple type sometimes
  map(zip(components, doms, codoms)) do (component, dom, codom)
    ACSetTransformation(component, dom, codom; cat)
  end |> collect
end
