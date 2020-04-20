using Markov
using Catlab
using Catlab.Doctrines
using Test

X = Ob(FreeCartesianCategory, :Float64)
u = Hom(x->x*rand(), X, X)

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
meantest(1/2, 10000, 1e-1) do i
    crand(u⋅mcopy(X)⋅(id(X)⊗delete(X)), 1)[1]
end
