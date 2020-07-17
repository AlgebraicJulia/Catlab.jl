using Test

@testset "GenerateJuliaPrograms" begin
  include("GenerateJuliaPrograms.jl")
end

@testset "ParseJuliaPrograms" begin
  include("ParseJuliaPrograms.jl")
end

@testset "ParseRelations" begin
  include("ParseRelations.jl")
end
