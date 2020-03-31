using Test

@testset "AlgebraicNets" begin
  include("core/AlgebraicNets.jl")
end

@testset "MathFormulas.jl" begin
  include("core/MathFormulas.jl")
end
