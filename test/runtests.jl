using Base.Test

@testset "Syntax" begin
  include("Syntax.jl")
end

@testset "Diagram.Wiring" begin
  include("diagram/Wiring.jl")
end
