using Base.Test

@testset "Syntax" begin
  include("Syntax.jl")
end

@testset "Diagram.AbstractWiring" begin
  include("diagram/AbstractWiring.jl")
end

@testset "Diagram.TikZ" begin
  include("diagram/TikZ.jl")
end
