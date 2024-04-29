using Test

@testset "GATs" begin
include("gats/GATs.jl")
end

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

@testset "Programs" begin
  include("programs/Programs.jl")
end

@testset "Sheaves" begin
  include("sheaves/sheaves.jl")
end

@testset "Decorated" begin
  include("decorated/Decorated.jl")
end