module TestCategoricalAlgebra

using Test

@testset "Misc" begin
  include("Misc/Permutations.jl")
  include("Misc/Matrices.jl")
  include("Misc/FinRelations.jl")
end

@testset "Categories" begin
  include("Cats/Paths.jl")
  include("Cats/Categories.jl")
  include("Cats/FinCats.jl")
  include("Cats/Functors.jl")
  include("Cats/FreeDiagrams.jl")
  include("Cats/CommutativeDiagrams.jl")
  # include("Cats/Limits.jl")
  # include("Cats/Diagrams.jl")

end

@testset "Sets" begin
  include("SetCats/SkelFinSetCat.jl")
  include("SetCats/VarFunctions.jl")
  # include("SetCats/Subsets.jl")
  # include("SetCats/SetCLimits.jl")
  # include("SetCats/FinCLimits.jl")
  # include("SetCats/VarFnLimits.jl")
end

@testset "CSets" begin
  include("CSetCats/ACSetLimits.jl")
  # include("CSetCats/ACSetsGATsInterop.jl")
  # include("CSetCats/ACSetTransformations.jl")
  # include("CSetCats/CSets.jl")
  # include("CSetCats/HomSearch.jl")
  # include("CSetCats/CatElements.jl")
  # include("CSetCats/Chase.jl")
  # include("CSetCats/FunctorialDataMigrations.jl")
  # include("CSetCats/StructuredCospans.jl")
  # include("CSetCats/SliceCategories.jl")
end


end # module
