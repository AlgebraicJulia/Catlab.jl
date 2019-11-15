using Test

@testset "JuliaPrograms" begin
  include("JuliaPrograms.jl")
end

@testset "AlgebraicNets" begin
  include("AlgebraicNets.jl")
end

@testset "ExpressionTrees" begin
  include("ExpressionTrees.jl")
end
