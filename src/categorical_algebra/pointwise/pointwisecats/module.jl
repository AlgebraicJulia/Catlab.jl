module PointwiseCats 
export ACSetCat

import ACSets

import ....Theories: dom, codom
import ..CSets: ACSetCategory
using ...Cats: obtype, homtype
using Reexport

""" 
Subtyped by structs which are models of categories whose objects are ACSets,
e.g. `CSetCat`, `ACSetCat`, `CParCat`, `ACSetLoose`, etc."""
abstract type AbsACSetCat end 

ACSets.acset_schema(x::AbsACSetCat) = ACSets.acset_schema(x.constructor())
ACSets.DenseACSets.attr_type(x::AbsACSetCat, f::Symbol) = ACSets.DenseACSets.attr_type(x.constructor(), f)
dom(c::AbsACSetCat, x) = dom(acset_schema(c), x)
codom(c::AbsACSetCat, x) = codom(acset_schema(c), x)
ACSets.DenseACSets.attrtype_type(model::AbsACSetCat, T::Symbol) = 
  ACSets.DenseACSets.attrtype_type(model.constructor(), T)


include("CSetCats.jl")
@reexport using .CSetCats

include("ACSetCats.jl")
@reexport using .ACSetCats

include("VarACSetCats.jl")
@reexport using .VarACSetCats

include("MADCSetCats.jl")
@reexport using .MADCSetCats

include("MADACSetCats.jl")
@reexport using .MADACSetCats

include("MADVarACSetCats.jl")
@reexport using .MADVarACSetCats

include("ACSetLooseCats.jl")
@reexport using .ACSetLooseCats

# todo CParCats

include("CatsOfACSet.jl")
@reexport using .CatsOfACSet


include("InferCat.jl")


end # module
