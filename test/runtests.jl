using Test

@testset "GATs" begin
  include("Meta.jl")
  include("GAT.jl")
end

@testset "Syntax" begin
  include("Syntax.jl")
  include("Present.jl")
end

@testset "Doctrines" begin
  include("Doctrine.jl")
end

@testset "Diagrams" begin
  include("diagram/Diagram.jl")
end

@testset "Algebra" begin
  include("algebra/Algebra.jl")
end
