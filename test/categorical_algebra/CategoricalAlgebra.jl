module TestCategoricalAlgebra

using Test

@testset "FreeDiagrams" begin
  include("FreeDiagrams.jl")
end

@testset "Limits" begin
  include("Limits.jl")
end

@testset "Matrices" begin
  include("Matrices.jl")
end

@testset "FinSets" begin
  include("FinSets.jl")
end

@testset "FinRelations" begin
  include("FinRelations.jl")
end

@testset "Permutations" begin
  include("Permutations.jl")
end

@testset "ACSets.jl" begin
  include("ACSets.jl")
  include("Graphs.jl")
end

@testset "PredicatedSets.jl" begin
  include("PredicatedSets.jl")
end

end
