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

include("Algebra.jl")
include("Diagram.jl")
