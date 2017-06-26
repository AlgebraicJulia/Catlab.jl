# Third-party tests.
include("Networks.jl")

@testset "Diagram.Wiring" begin
  include("Wiring.jl")
end

@testset "Diagram.TikZ" begin
  include("TikZ.jl")
  include("TikZWiring.jl")
end
