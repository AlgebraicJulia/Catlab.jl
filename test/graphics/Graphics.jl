using Test

@testset "Layouts" begin
  include("WiringDiagramLayouts.jl")
end

@testset "Graphviz" begin
  include("Graphviz.jl")
  include("GraphvizWiringDiagrams.jl")
end

@testset "Compose" begin
  include("ComposeWiringDiagrams.jl")
end

@testset "TikZ" begin
  include("TikZ.jl")
  include("TikZWiringDiagrams.jl")
end

@testset "yFiles" begin
  include("YFilesWiringDiagrams.jl")
end
