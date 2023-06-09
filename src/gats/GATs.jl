""" Generalized algebraic theories (GATs) in Julia.
"""
module GATs

using Reexport

include("MetaUtils.jl")
include("TheoriesInstances.jl")
include("SyntaxSystems.jl")
include("Rewriting.jl")
include("Presentations.jl")

@reexport using .TheoriesInstances
@reexport using .SyntaxSystems
@reexport using .Rewriting
@reexport using .Presentations

end
