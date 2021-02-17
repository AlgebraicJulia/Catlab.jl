module TestGraphs

using Test

@testset "BasicGraphs" begin
  include("BasicGraphs.jl")
end

@testset "BipartiteGraphs" begin
  include("BipartiteGraphs.jl")
end

@testset "PropertyGraphs" begin
  include("PropertyGraphs.jl")
end

@testset "GraphAlgorithms" begin
  include("GraphAlgorithms.jl")
end

end
