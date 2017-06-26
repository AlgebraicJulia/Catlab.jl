# Third-party tests.
include("diagram/Networks.jl")

@testset "Diagram.Wiring" begin
  include("diagram/Wiring.jl")
end

@testset "Diagram.TikZ" begin
  include("diagram/TikZ.jl")
  include("diagram/TikZWiring.jl")
end
