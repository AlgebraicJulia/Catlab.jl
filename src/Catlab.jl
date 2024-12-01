module Catlab

using Reexport

include("theories/Theories.jl")
include("ACSetsGATsInterop.jl")
include("graphs/Graphs.jl")
include("basic_sets/BasicSets.jl")
include("categorical_algebra/CategoricalAlgebra.jl")
# include("wiring_diagrams/WiringDiagrams.jl")
# include("graphics/Graphics.jl")
# include("programs/Programs.jl")

@reexport using .Theories
@reexport using .Graphs
@reexport using .BasicSets
@reexport using .CategoricalAlgebra
# @reexport using .WiringDiagrams
# @reexport using .Graphics
# @reexport using .Programs

end
