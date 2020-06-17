module TestCategoricalAlgebra

using Test

@testset "FinSets" begin
  include("FinSets.jl")
end

@testset "Permutations" begin
  include("Permutations.jl")
end

end
