module NatTrans 

using Reexport 

include("NatTrans.jl")

include("IdTrans.jl")
@reexport using .IdTrans

include("OpTrans.jl")
@reexport using .OpTrans

include("MapTrans.jl")
@reexport using .MapTrans

include("TwoCat.jl")
@reexport using .TwoCat


end # module