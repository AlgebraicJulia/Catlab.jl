module FinFunctors 
using Reexport

include("FinFunctors.jl")
include("IdFinFunctor.jl")
include("OpFinFunctor.jl")
include("FinDomMap.jl")
include("CompFinFunctor.jl")
# include("FreeDiagramFunctors.jl")

@reexport using .IdFinFunctor
@reexport using .OpFinFunctor
@reexport using .FinDomMap
@reexport using .CompFinFunctor
# @reexport using .FreeDiagramFunctors

end # module
