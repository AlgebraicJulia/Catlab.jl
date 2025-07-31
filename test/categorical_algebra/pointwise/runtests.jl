
using Test 

@testset "CSetCats" begin
  include("csetcats/runtests.jl")
end

@testset "ACSetCats" begin
  include("acsetcats/runtests.jl")
end 

@testset "VarACSetCats" begin
  include("varacsetcats/runtests.jl")
end 

# @testset "LabeledCSets" begin
  # include("LabeledCSets/Limits.jl")
# end

@testset "MADCats" begin
  include("madcats/runtests.jl")
end

@testset "MADVarACats" begin
  include("madvaracsetcats/HomSearch.jl")
end


# @testset "LooseACSetCats" begin
  # include("LooseACSetCats/HomSearch.jl")
# end

# @testset "LooseVarACSetCats" begin
  # include("LooseVarACSetCats/ACSetTransformations.jl")
# end

