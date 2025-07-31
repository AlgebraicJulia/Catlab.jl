module FinFunctors 
using Reexport

include("FinFunctors.jl")

include("IdFinFunctor.jl")
@reexport using .IdFinFunctor

include("OpFinFunctor.jl")
@reexport using .OpFinFunctor

include("FinDomMap.jl")
@reexport using .FinDomMap

include("CompFinFunctor.jl")
@reexport using .CompFinFunctor

include("FreeDiagramFunctors.jl")
@reexport using .FreeDiagramFunctors

end # module
