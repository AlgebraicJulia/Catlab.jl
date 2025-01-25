
using Test

@testset "SetsInterop" begin
  include("SetsInterop.jl")
end

@testset "SkelFinSet" begin
  include("skelfinset/Limits.jl")

  include("skelfinset/Colimits.jl")
end

@testset "SetC" begin

  include("setcats/Sets.jl")

  include("setcats/Limits.jl")

  include("setcats/Colimits.jl")

end

@testset "FinSetC" begin

  include("finsetcat/Limits.jl")

  include("finsetcat/Colimits.jl")
end

@testset "VarFunctions" begin

  include("varfunctions/VarFunctions.jl")

  include("varfunctions/VarFnLimits.jl")
end

@testset "SubSets" begin
  include("SubSets.jl")
end
