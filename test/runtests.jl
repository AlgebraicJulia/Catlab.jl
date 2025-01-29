using Test

include("ACSetsGATsInterop.jl")

@testset "Theories" begin
  include("theories/runtests.jl")
end

@testset "Graphs" begin
  include("graphs/runtests.jl") 
end

@testset "BasicSets" begin
  include("basic_sets/runtests.jl")
end

@testset "CategoricalAlgebra" begin
  include("categorical_algebra/runtests.jl")
end

@testset "WiringDiagrams" begin
  include("wiring_diagrams/runtests.jl")
end

@testset "ADTs" begin
  include("adts/runtests.jl")
end

@testset "Programs" begin
  include("programs/runtests.jl")
end

@testset "Parsers" begin
  include("parsers/runtests.jl")
end

@testset "Sheaves" begin
  include("sheaves/runtests.jl")
end
