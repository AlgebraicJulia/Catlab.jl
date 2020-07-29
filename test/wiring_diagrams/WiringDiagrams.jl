using Test

@testset "Core" begin
  include("Directed.jl")
  include("Undirected.jl")
end

@testset "Monoidal" begin
  include("MonoidalDirected.jl")
  include("MonoidalUndirected.jl")
end

@testset "Algorithms" begin
  include("Algorithms.jl")
end

@testset "Expressions" begin
  include("Expressions.jl")
end

@testset "Serialization" begin
  include("GraphML.jl")
  include("JSON.jl")
end
