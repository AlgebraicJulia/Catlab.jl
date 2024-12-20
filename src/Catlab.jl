module Catlab

using Reexport

include("01_theories/module.jl")
include("ACSetsGATsInterop.jl") # depends on Theories but is not a theory
include("02_graphs/Graphs.jl")
include("03_basic_sets/module.jl")
include("04_categorical_algebra/module.jl")
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

end # module
