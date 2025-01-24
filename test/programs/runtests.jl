using Test

@testset "GenerateJuliaPrograms" begin
  include("GenerateJuliaPrograms.jl")
end

@testset "ParseJuliaPrograms" begin
  include("ParseJuliaPrograms.jl")
end

@testset "RelationalPrograms" begin
  include("RelationalPrograms.jl")
end
