using Test

@testset "WiringCore" begin
  include("Core.jl")
end

@testset "WiringAlgorithms" begin
  include("Algorithms.jl")
end

@testset "GraphML" begin
  include("GraphML.jl")
end
