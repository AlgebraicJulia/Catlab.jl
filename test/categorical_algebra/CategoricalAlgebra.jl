module TestCategoricalAlgebra

using Test

@testset "Permutations" begin
  include("Permutations.jl")
end

@testset "Matrices" begin
  include("Matrices.jl")
end


@testset "Categories" begin
  include("Categories.jl")
  # include("FinCats.jl")
end

@testset "FreeDiagrams" begin
  include("FreeDiagrams.jl")
end

include("Limits.jl")

@testset "Sets" begin
  include("Sets.jl")
  include("SetFunctions.jl")
  include("FinSets.jl")
  include("FinFunctions.jl")
  include("Subsets.jl")
end

@testset "Limits" begin
  include("FinCLimits.jl")
end


@testset "Relations" begin
  include("FinRelations.jl")
end

# @testset "CSets" begin
#   include("ACSetsGATsInterop.jl")
#   include("CSets.jl")
#   include("HomSearch.jl")
#   include("CatElements.jl")
# end

# @testset "Diagrams" begin
#   include("Diagrams.jl")
#   include("CommutativeDiagrams.jl")
# end

# @testset "Chase" begin
#   include("Chase.jl")
# end

# @testset "FunctorialDataMigrations" begin
#   include("FunctorialDataMigrations.jl")
# end

# @testset "StructuredCospans" begin
#   include("StructuredCospans.jl")
# end

# @testset "SliceCategories" begin
#   include("SliceCategories.jl")
# end


end
