
using Test 

@testset "CSetCats" begin
  include("CSetCats/ACSetTransformations.jl")
  include("CSetCats/Limits.jl")
  include("CSetCats/Colimits.jl")
  include("CSetCats/HomSearch.jl")
  include("CSetCats/MCO.jl")
  include("CSetCats/VMSearch.jl")
end 

@testset "ACSetCats" begin
  include("ACSetCats/Colimits.jl")
  include("ACSetCats/HomSearch.jl")
  # include("ACSetCats/MCO.jl") # need to fix infer_acset_cat
end 

@testset "VarACSetCats" begin
  include("VarACSetCats/Colimits.jl") 
  include("VarACSetCats/HomSearch.jl")
  # include("VarACSetCats/MCO.jl")
end 

@testset "LooseACSetCats" begin
  # include("LooseACSetCats/HomSearch.jl")
end

@testset "MADCats" begin
  # include("MADCats/HomSearch.jl")
end

