module Catlab

include("core/Core.jl")
include("theories/Theories.jl")

include("categorical_algebra/IndexUtils.jl")
include("categorical_algebra/ACSetInterface.jl")
include("categorical_algebra/ACSetColumns.jl")
include("categorical_algebra/CSetDataStructures.jl")
include("categorical_algebra/Permutations.jl")
include("graphs/Graphs.jl")
include("categorical_algebra/CategoricalAlgebra.jl")

include("wiring_diagrams/WiringDiagrams.jl")
include("graphics/Graphics.jl")
include("programs/Programs.jl")

end
