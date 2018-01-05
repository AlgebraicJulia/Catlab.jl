using Base.Test

# Third-party tests.
@testset "External" begin
  include("external/Networks.jl")
end

@testset "Wiring" begin
  include("Wiring.jl")
  include("GraphML.jl")
end

@testset "Graphviz" begin
  include("Graphviz.jl")
  include("GraphvizWiring.jl")
end

@testset "TikZ" begin
  include("TikZ.jl")
  include("TikZWiring.jl")
end
