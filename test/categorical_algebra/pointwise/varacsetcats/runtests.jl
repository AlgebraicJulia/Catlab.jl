using Test

@testset "ACSetTransformations" begin
  include("ACSetTransformations.jl") 
end 

@testset "Colimits" begin
  include("Colimits.jl") 
end

@testset "HomSearch" begin
  include("HomSearch.jl")
end

@testset "DataMigrations" begin
  include("DataMigrations.jl")
end

@testset "Subobjects" begin
  include("Subobjects.jl")
end
@testset "MCO" begin
  include("MCO.jl")
end 
