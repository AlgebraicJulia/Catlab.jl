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
include("doctrines/Doctrines.jl")
include("wiring_diagrams/WiringDiagrams.jl")
include("graphics/Graphics.jl")
include("algebra/Algebra.jl")

end
