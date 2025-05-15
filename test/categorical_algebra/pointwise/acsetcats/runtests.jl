using Test 

@testset "ACSetTransformations" begin
  include("ACSetTransformations.jl")
end

@testset "ACSetFunctors" begin
  include("ACSetFunctors.jl")
end

@testset "Colimits" begin
  include("Colimits.jl")
end

@testset "HomSearch" begin
  include("HomSearch.jl")
end

@testset "FunctorialDataMigrations" begin
  include("FunctorialDataMigrations.jl")
end

@testset "Dynamic" begin
  include("Dynamic.jl") 
end

@testset "Dynamic" begin
  include("StructuredCospans.jl")
end
