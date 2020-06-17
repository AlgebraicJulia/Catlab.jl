module TestCategoricalAlgebra

using Test

@testset "ShapeDiagrams" begin
  include("ShapeDiagrams.jl")
end

@testset "FinSets" begin
  include("FinSets.jl")
end

@testset "Permutations" begin
  include("Permutations.jl")
end

end
