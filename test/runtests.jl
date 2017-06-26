using Base.Test

@testset "GAT" begin
  include("GAT.jl")
end

@testset "Syntax" begin
  include("Syntax.jl")
end

@testset "Presentation" begin
  include("Presentation.jl")
end

@testset "Doctrine" begin
  include("Doctrine.jl")
end

include("diagram/Diagram.jl")
include("algebra/Algebra.jl")
