module Functors 

using Reexport 

include("Functors.jl")

include("IdFunctor.jl")
@reexport using .IdFunctor

include("CompFunctor.jl")
@reexport using .CompFunctor

include("CallFunctor.jl")
@reexport using .CallFunctor

include("OpFunctor.jl")
@reexport using .OpFunctor

end # module
