using Test 

@testset "SetsInterop" begin
  include("SetsInterop.jl")
end

@testset "CSetCats" begin
  include("CSetCats/runtests.jl")
end 

@testset "ACSetCats" begin
  include("acsetcats/runtests.jl")
end 

@testset "VarACSetCats" begin
  include("varacsetcats/runtests.jl")
end 

@testset "LabeledCSets" begin
  include("labeledcsetcats/runtests.jl")
end

@testset "MADCats" begin
  include("madacsetcats/runtests.jl")
end

@testset "LooseACSetCats" begin
  include("looseacsetcats/runtests.jl")
end

@testset "LooseVarACSetCats" begin
  include("loosevaracsetcats/runtests.jl")
end
