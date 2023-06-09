using Test

@testset "TheoriesInstances" begin
  include("MetaUtils.jl")
  include("TheoriesInstances.jl")
end

@testset "SyntaxSystems" begin
  include("SyntaxSystems.jl")
end

@testset "Presentations" begin
  include("Presentations.jl")
end
