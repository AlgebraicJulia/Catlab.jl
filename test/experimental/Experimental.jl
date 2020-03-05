using Test

@testset "AlgebraicNets" begin
  include("AlgebraicNets.jl")
end

@testset "MathFormulas" begin
  include("MathFormulas.jl")
end

@testset "MarkovCategories" begin
  include("Markov.jl")
end
