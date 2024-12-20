module PointwiseCats 
export ACSetCat

import ..CSets: ACSetCategory
using ...Cats: obtype, homtype
using Reexport

abstract type AbsACSetCat{EC,AC,PC,O,H,AT,OP,A} end

ACSetCategory(x::AbsACSetCat{EC,AC,PC,O,H,AT,OP,A}) where {EC,AC,PC,O,H,AT,OP,A} =
  ACSetCategory{EC,AC,PC,O,H,AT,A,OP}(x)


include("CSetCats.jl")
@reexport using .CSetCats

include("ACSetCats.jl")
@reexport using .ACSetCats

include("CatsOfACSet.jl")
@reexport using .CatsOfACSet

end # module
