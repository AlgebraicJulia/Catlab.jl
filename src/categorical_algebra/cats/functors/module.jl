
module Functors 
using Reexport

include("Functors.jl")
include("IdFunctor.jl")
include("CompFunctor.jl")
include("CallFunctor.jl")
include("OpFunctor.jl")

@reexport using .IdFunctor
@reexport using .CompFunctor
@reexport using .CallFunctor
@reexport using .OpFunctor

end # module
