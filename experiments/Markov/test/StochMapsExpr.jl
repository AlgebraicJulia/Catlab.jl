using Markov
using Catlab
using Catlab.Doctrines
using Test

X = Ob(FreeCartesianCategory, :Float64)
u = Hom(x->x*rand(), X, X)

u₀ = Hom(()->rand(), munit(FreeCartesianCategory.Ob), X)
crand(u₀⊗u₀)

meantest(f::Function, μ::Real, n::Int, ϵ::Real) = begin
    μ̂ = sum(map(f, 1:n))/n
    @test μ - ϵ < μ̂
    @test μ̂ < μ + ϵ
end

meantest(1/1, 10000, 1e-1) do i
    crand(((u⊗u)⋅braid(X,X)), 1,2)[1]
end
meantest(1/2, 10000, 1e-1) do i
    crand(((u⊗u)⋅braid(X,X)), 1,2)[2]
end
meantest(1/1, 10000, 1e1) do i
    crand(mcopy(X),2)[1]
end
meantest(1/1, 10000, 1e1) do i
    crand(mcopy(X),2)[2]
end

@test crand(delete(X), 1) == ()
@test crand(u⋅delete(X), 1) == ()
meantest(1/2, 1000, 1e-1) do i
    crand(u⋅mcopy(X)⋅(id(X)⊗delete(X)), 1)[1][1]
end

@testset "Uniforms" begin
  u₀ = Hom(()->rand(), munit(FreeCartesianCategory.Ob), X)
  @test 0 <= crand(u, 1.0) <= 1.0
  @test 0 <= crand(u, 2) <= 2
  @test compose(u,u).args |> length == 2
  @test dom(compose(u,u)) == X
  @test codom(compose(u,u)) == X
  @test 0 <= crand(compose(u,u), 0.5) <= 1/2
  @test 0 <= crand(u₀) <= 1
  @test crand(u₀⊗u₀) |> length == 2
  @test crand(u⊗u₀, 1.0) |> length == 2
  @test crand(u₀⊗u, 1.0) |> length == 2
  @test crand(otimes(u₀,u₀,u), 2.0) |> length == 3
  @test crand(otimes(u₀,u,u₀), 2.0) |> length == 3
  @test crand(otimes(u₀,u,u), 1.0, 2.0) |> length == 3
  @test crand(otimes(u₀,u,u)⋅otimes(u,u,u), 1.0, 2.0) |> length == 3
  @test crand(otimes(u,u,u), 1.0, 2.0, 3.0) |> length == 3
end

@test crand(compose(id(X), id(X), id(X)), 1)[1] == 1
