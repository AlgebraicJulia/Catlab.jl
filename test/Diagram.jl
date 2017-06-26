@testset "Diagram.Wiring" begin
  include("diagram/Networks.jl")
  include("diagram/Wiring.jl")
end

@testset "Diagram.TikZ" begin
  include("diagram/TikZ.jl")
end

@testset "Diagram.TikZWiring" begin
  include("diagram/TikZWiring.jl")
end
