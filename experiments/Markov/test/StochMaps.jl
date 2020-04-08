using Test
using Distributions
using Markov
using Markov.StochMaps
import Markov.StochMaps: compose, otimes, ⋅, ⊗, dom, codom
import Base: show

@testset "Uniforms" begin
  u = StochGenerator(StochFloat, StochFloat, (x)->Uniform(0,x...))
  u₀ = StochGenerator(StochMunit, StochFloat, ()->Uniform(0,1))
  @test 0 <= crand(u, 1.0) <= 1.0
  @test 0 <= crand(u, 2) <= 2
  @test compose(u,u).maps |> length == 2
  @test dom(compose(u,u)).types == DataType[Float64]
  @test codom(compose(u,u)).types == DataType[Float64]
  @test 0 <= crand(compose(u,u), 0.5) <= 1/2
  @test crand(Constant(1.5)) == 1.5
  @test 0 <= crand(u₀) <= 1
  @test crand(u₀⊗u₀) |> length == 2
  @test crand(u⊗u₀, 1.0) |> length == 2
  @test crand(u₀⊗u, 1.0) |> length == 2
  @test crand(otimes(u₀,u₀,u), 2.0) |> length == 3
  @test crand(otimes(u₀,u,u₀), 2.0) |> length == 3
  @test crand(otimes(u₀,u,u), 1.0, 2.0) |> length == 3
  @test crand(otimes(u₀,u,u)⋅otimes(u,u,u), 1.0, 2.0) |> length == 3
  @test crand(otimes(u,u,u), 1.0, 2.0, 3.0) |> length == 3
  @test 0 <= crand(compose(u), 1.0) <=1
end

@testset "Printing" begin
  uℓ = StochGenerator(StochFloat, StochFloat, x->Uniform(x, 1))
  @test string(uℓ⋅uℓ)== "StochComposite(2): StochDom(Float64) → StochDom(Float64)"
  @test string(uℓ⊗uℓ) == "StochProduct(2): StochDom(Float64×Float64) → StochDom(Float64×Float64)"

  @test string(StochFloat⊗StochFloat) == "StochDom(Float64×Float64)"
  @test string(StochFloat⊗StochFloat⊗StochDom([Int64])) == "StochDom(Float64×Float64×Int64)"
  @test string(StochBraid(StochFloat, StochFloat)) == "StochBraid(Float64,Float64)"
  @test string(StochBraid(StochFloat, StochFloat⊗StochFloat)) == "StochBraid(Float64,Float64×Float64)"
end
