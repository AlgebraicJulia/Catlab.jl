module Catlab

using Reexport

include("theories/Theories.jl")
include("ACSetsGATsInterop.jl") # This should be upstreamed to an extension of ACSets.jl
include("graphs/Graphs.jl")
include("basic_sets/module.jl")
include("categorical_algebra/module.jl")
include("wiring_diagrams/WiringDiagrams.jl")
include("graphics/Graphics.jl")
include("adts/ADTs.jl")
include("programs/Programs.jl")
include("parsers/Parsers.jl")
include("sheaves/Sheaves.jl")

@reexport using .Theories
@reexport using .Graphs
@reexport using .BasicSets
@reexport using .CategoricalAlgebra
@reexport using .WiringDiagrams
@reexport using .Graphics
@reexport using .Programs
@reexport using .Parsers
@reexport using .Sheaves

end
