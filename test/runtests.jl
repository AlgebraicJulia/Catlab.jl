using Base.Test

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

include("diagram/Diagram.jl")
include("algebra/Algebra.jl")
