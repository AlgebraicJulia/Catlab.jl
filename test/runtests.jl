using Test

@testset "Theories" begin
  include("theories/Theories.jl")
end

@testset "CategoricalAlgebra" begin
  include("categorical_algebra/CategoricalAlgebra.jl")
end

@testset "Graphs" begin
  include("graphs/Graphs.jl")
end

@testset "WiringDiagrams" begin
  include("wiring_diagrams/WiringDiagrams.jl")
end

@testset "Graphics" begin
  include("graphics/Graphics.jl")
end

@testset "ADTs" begin
  include("ADTs/ADTs.jl")
end

@testset "Programs" begin
  include("programs/Programs.jl")
end

@testset "Parsers" begin
  include("parsers/Parsers.jl")
end