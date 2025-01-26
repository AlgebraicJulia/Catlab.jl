
using Test

@testset "SetsInterop" begin
  include("SetsInterop.jl")
end

@testset "SkelFinSet" begin
  include("skelfinset/runtests.jl")
end

@testset "SetC" begin
  include("setcats/runtests.jl")
end

@testset "FinSetC" begin
  include("finsetcat/runtests.jl")
end

@testset "VarFunctions" begin
  include("varfunctions/runtests.jl")
end

@testset "SubSets" begin
  include("SubSets.jl")
end
