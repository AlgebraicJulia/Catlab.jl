module PointwiseCats 
export ACSetCat

import ..CSets: ACSetCategory
using ...Cats: obtype, homtype
using Reexport

""" 
Subtyped by structs which are models of categories whose objects are ACSets,
e.g. `CSetCat`, `ACSetCat`, `CParCat`, `ACSetLoose`, etc."""
abstract type AbsACSetCat end 

include("CSetCats.jl")
@reexport using .CSetCats

include("ACSetCats.jl")
@reexport using .ACSetCats

include("VarACSetCats.jl")
@reexport using .VarACSetCats

include("CatsOfACSet.jl")
@reexport using .CatsOfACSet

end # module
