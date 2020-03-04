using Test

@testset "AlgebraicNets" begin
  include("AlgebraicNets.jl")
end

@testset "ExpressionTrees" begin
  include("ExpressionTrees.jl")
end

@testset "MarkovCategories" begin
  include("Markov.jl")
end
