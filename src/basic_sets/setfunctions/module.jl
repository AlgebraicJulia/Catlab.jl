module SetFunctions

using Reexport

include("SetFunctions.jl")
include("IdFunction.jl")
include("CompFunction.jl")
include("ConstFn.jl")
include("ConstEither.jl")
include("PredFn.jl")
include("Callable.jl")
include("Force.jl")

@reexport using .IdFunction
@reexport using .CompFn
@reexport using .ConstFn
@reexport using .ConstEitherFn
@reexport using .PredFn
@reexport using .CallableFn
@reexport using .Force

end # module
