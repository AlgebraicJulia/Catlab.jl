using Test

@testset "ParserCore" begin
  include("ParserCore.jl")
end

@testset "RelationalParser" begin
  include("RelationalParser.jl")
end