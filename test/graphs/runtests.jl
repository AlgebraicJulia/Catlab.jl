module TestGraphs

using Test

@testset "BasicGraphs" begin
  include("BasicGraphs.jl")
end

@testset "BipartiteGraphs" begin
  include("BipartiteGraphs.jl")
end

@testset "NamedGraphs" begin
  include("NamedGraphs.jl")
end

@testset "PropertyGraphs" begin
  include("PropertyGraphs.jl")
end

@testset "GraphAlgorithms" begin
  include("GraphAlgorithms.jl")
end

@testset "GraphGenerators" begin
  include("GraphGenerators.jl")
end

@testset "GraphSearching" begin
  include("GraphSearching.jl")
end

end
