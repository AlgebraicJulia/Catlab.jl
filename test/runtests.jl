using Test

# include("aqua.jl") # can uncomment once PR is more complete

# @testset "Theories" begin
#   include("theories/Theories.jl") # TO SAVE TIME
# end

# @testset "Graphs" begin
  # include("graphs/Graphs.jl") # TO SAVE TIME
# end

@testset "BasicSets" begin
  include("basic_sets/BasicSets.jl")
end

@testset "CategoricalAlgebra" begin
  include("categorical_algebra/CategoricalAlgebra.jl")
end

# @testset "WiringDiagrams" begin
#   include("wiring_diagrams/WiringDiagrams.jl")
# end

# @testset "Graphics" begin
#   include("graphics/Graphics.jl")
# end

# @testset "Programs" begin
#   include("programs/Programs.jl")
# end
