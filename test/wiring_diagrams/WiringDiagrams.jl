using Test

@testset "Core" begin
  include("Core.jl")
end

@testset "Algorithms" begin
  include("Algorithms.jl")
end

@testset "GraphML" begin
  include("GraphML.jl")
end
