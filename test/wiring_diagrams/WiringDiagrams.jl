using Test

@testset "Core" begin
  include("Core.jl")
end

@testset "Layers" begin
  include("Layers.jl")
end

@testset "Algorithms" begin
  include("Algorithms.jl")
end

@testset "GraphML" begin
  include("GraphML.jl")
end

@testset "JSON" begin
  include("JSON.jl")
end

@testset "yFiles" begin
  include("YFiles.jl")
end
