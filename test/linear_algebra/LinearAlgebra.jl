using Test

@testset "TensorNetworks" begin
  include("TensorNetworks.jl")
end

@testset "GraphicalLinearAlgebra" begin
  include("GLA.jl")
  include("StructuredGLA.jl")
end
