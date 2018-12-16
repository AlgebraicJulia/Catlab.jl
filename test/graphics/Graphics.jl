using Test

@testset "Graphviz" begin
  include("Graphviz.jl")
  include("GraphvizWiring.jl")
end

@testset "TikZ" begin
  include("TikZ.jl")
  include("TikZWiring.jl")
end
