using Test 

@testset "Sets" begin
  include("Sets.jl")
end

@testset "FinSets" begin
  include("FinSets.jl")
end

@testset "SetFunctions" begin
  include("SetFunctions.jl")
end

@testset "FinFunctions" begin
  include("FinFunctions.jl")
end
