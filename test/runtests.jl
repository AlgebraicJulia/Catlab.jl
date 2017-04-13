using Base.Test

@testset "GAT" begin
  include("GAT.jl")
end

@testset "Syntax" begin
  include("Syntax.jl")
end

@testset "Doctrine" begin
  include("Doctrine.jl")
end

@testset "Algebra" begin
  include("Algebra.jl")
end

include("Diagram.jl")
