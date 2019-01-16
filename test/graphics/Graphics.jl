using Test

@testset "Graphviz" begin
  include("Graphviz.jl")
  include("GraphvizWiringDiagrams.jl")
end

@testset "TikZ" begin
  include("TikZ.jl")
  include("TikZWiringDiagrams.jl")
end
