module TestCategoricalAlgebra

using Test

@testset "Categories" begin
  include("Categories.jl")
  include("FinCats.jl")
end

@testset "FreeDiagrams" begin
  include("FreeDiagrams.jl")
end

@testset "Limits" begin
  include("Limits.jl")
end

@testset "Matrices" begin
  include("Matrices.jl")
end

@testset "Sets" begin
  include("Sets.jl")
  include("FinSets.jl")
end

@testset "Relations" begin
  include("FinRelations.jl")
end

@testset "Permutations" begin
  include("Permutations.jl")
end

@testset "CSets" begin
  include("CSetDataStructures.jl")
  include("CSets.jl")
  include("CatElements.jl")
end

@testset "Diagrams" begin
  include("Diagrams.jl")
  include("CommutativeDiagrams.jl")
end

@testset "DataMigrations" begin
  include("DataMigrations.jl")
end

@testset "StructuredCospans" begin
  include("StructuredCospans.jl")
end

@testset "DPO" begin
  include("DPO.jl")
end

@testset "Slices" begin
  include("Slices.jl")
end

@testset "Chase" begin
  include("Chase.jl")
end

end
