using Test

@testset "Wiring" begin
  include("Wiring.jl")
  include("Algorithms.jl")
end

@testset "GraphML" begin
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
