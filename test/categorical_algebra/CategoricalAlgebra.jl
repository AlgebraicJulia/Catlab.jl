module TestCategoricalAlgebra

using Test

@testset "Misc" begin
  include("Misc/Permutations.jl")
  include("Misc/Matrices.jl")
  include("Misc/FinRelations.jl")
end

@testset "Categories" begin
  include("Cats/Categories.jl")
  # include("Cats/FinCats.jl")
end

@testset "FreeDiagrams" begin
  # include("Cats/FreeDiagrams.jl")
end

include("Cats/Limits.jl")

@testset "Sets" begin
  include("SetCats/Sets.jl")
  include("SetCats/SetFunctions.jl")
  include("SetCats/FinSets.jl")
  include("SetCats/FinFunctions.jl")
  include("SetCats/Subsets.jl")
  include("SetCats/FinCLimits.jl")
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
