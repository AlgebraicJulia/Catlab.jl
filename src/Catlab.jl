module Catlab

using Reexport

# Core modules
include("Meta.jl")
include("GAT.jl")
include("Syntax.jl")
include("Rewrite.jl")
include("Present.jl")

@reexport using .GAT
@reexport using .Syntax
@reexport using .Rewrite
@reexport using .Present

# Additional modules
include("doctrine/Doctrine.jl")
include("diagram/Diagram.jl")
include("algebra/Algebra.jl")

end
