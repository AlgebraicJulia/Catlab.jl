module TestGraphs

using Test

@testset "BasicGraphs" begin
  include("BasicGraphs.jl")
end

@testset "PropertyGraphs" begin
  include("PropertyGraphs.jl")
end

end
