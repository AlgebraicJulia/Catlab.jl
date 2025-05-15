using Test 

@testset "ACSetTransformations" begin
  include("ACSetTransformations.jl")
end

@testset "ACSetFunctors" begin
  include("ACSetFunctors.jl")
end

@testset "Limits" begin
  include("Limits.jl")
end
@testset "Colimits" begin
  include("Colimits.jl")
end
@testset "HomSearch" begin
  include("HomSearch.jl")
end
@testset "MCO" begin
  include("MCO.jl")
end
@testset "VMSearch" begin
  include("VMSearch.jl")
end
@testset "CatElements" begin
  include("CatElements.jl")
end
@testset "Subobjects" begin
  include("Subobjects.jl")
end
@testset "Chase" begin
  include("Chase.jl")
end
@testset "FunctorialDataMigrations" begin
  include("FunctorialDataMigrations.jl")
end
@testset "Yoneda" begin
  include("Yoneda.jl")
end
@testset "Dynamic" begin
  include("Dynamic.jl")
end
@testset "StructuredCospans" begin
  include("StructuredCospans.jl")
end

