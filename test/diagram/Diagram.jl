# Third-party tests.
include("external/Networks.jl")

@testset "Diagram" begin
  include("Wiring.jl")
  include("GraphML.jl")
end

@testset "Diagram.Graphviz" begin
  include("Graphviz.jl")
  include("GraphvizWiring.jl")
end

@testset "Diagram.TikZ" begin
  include("TikZ.jl")
  include("TikZWiring.jl")
end
