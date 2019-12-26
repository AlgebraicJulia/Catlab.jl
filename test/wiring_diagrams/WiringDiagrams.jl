using Test

@testset "Core" begin
  include("Core.jl")
end

@testset "Layers" begin
  include("Layers.jl")
end

@testset "Algebraic" begin
  include("Algebraic.jl")
end

@testset "Algorithms" begin
  include("Algorithms.jl")
end

@testset "Expressions" begin
  include("Expressions.jl")
end

@testset "GraphML" begin
  include("GraphML.jl")
end

@testset "JSON" begin
  include("JSON.jl")
end
