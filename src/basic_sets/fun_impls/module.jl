using Reexport 

include("IdFunction.jl")
@reexport using .IdFunction

include("FunctionCallable.jl")
@reexport using .CallableFn

include("ConstFn.jl")
@reexport using .ConstFn

include("CompFunction.jl")
@reexport using .CompFn

include("FinFnVector.jl")
@reexport using .FinFnVector

include("FinFnDict.jl")
@reexport using .FinFnDict

include("FinFunsAsFDFs.jl")
@reexport using .FinFunsAsFDFs

include("FDFsAsSetFuns.jl")
@reexport using .FDFsAsSetFuns
