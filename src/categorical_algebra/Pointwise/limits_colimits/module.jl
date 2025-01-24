module PointwiseLimitsColimits 

using StructEquality 

using ACSets 
using ACSets.DenseACSets: datatypes, attrtype_type

import .....Theories: ⊕, ⊗, ⋅
using ....BasicSets, ...Cats, ...SetCats
import ...Cats: limit, colimit, universal, product, initial, coproduct, terminal

using ..ACSetTransformations, ..CSets
using ..CSets: sets

include("LimitsColimits.jl")
include("Limits.jl")
include("Colimits.jl")

end # module
