module TestCategoricalAlgebra

using Test

@testset "Cats" begin
  include("cats/runtests.jl")
end 

@testset "SetCats" begin
  include("setcats/runtests.jl")
end 

@testset "Pointwise" begin
  include("pointwise/runtests.jl")
end

@testset "MiscCategoricalAlgebra" begin
  include("misc/runtests.jl")
end 

end # module
