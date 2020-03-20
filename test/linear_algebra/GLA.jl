module TestGraphicalLinearAlgebra
using Test

using Random
using IterativeSolvers

using Catlab, Catlab.Doctrines, Catlab.WiringDiagrams, Catlab.Programs
using Catlab.LinearAlgebra.GraphicalLinearAlgebra
import LinearAlgebra: norm, svd

import LinearMaps: BlockDiagonalMap, UniformScaling
using LinearOperators

# Doctrines
###########

A, B = Ob(FreeLinearFunctions, :A, :B)
f, g = Hom(:f, A, B), Hom(:g, A, B)

# Domains and codomains
@test dom(plus(f,g)) == A
@test codom(plus(f,g)) == B

# Unicode syntax
@test f+g == plus(f,g)

# Evaluation
############

# LinearMaps instance
#--------------------

f, g = LinearMap([0 1; 1 0]), LinearMap([1 2 3; 4 5 6; 7 8 9])
h, k = LinearMap([1 -1; -1 1; 0 1]), LinearMap([1 1; 2 2; 3 3])

x, y = [2, 1], [7, 3, 5]
@test (f⋅f)*x == f*(f*x)
@test (f⋅h)*x == h*(f*x)
@test (f⊕g)*[x;y] == [f*x; g*y]
@test braid(dom(f),dom(g)) * [x;y] == [y;x]

@test mcopy(dom(f))*x == [x;x]
@test delete(dom(f))*x == []
@test plus(dom(f))*[x;x] == 2x
@test zero(dom(f))*Float64[] == zero(x)

@test (h+k)*x == h*x + k*x
@test scalar(dom(f),3)*x == 3*x
@test antipode(dom(f))*x == -1*x
@test adjoint(g)*y == g'*y


# GMRES with LinearMaps
#----------------------

V, W = Ob(FreeLinearFunctions, :V, :W)
f, g, h = Hom(:f, V, W), Hom(:g, V, W), Hom(:h, W, W)

M = plus(f,g)⋅h
# M = plus(f,g)

d = Dict(f=>LinearMap([1 1 1 1; 2 2 2 3; 3 3 3 3.0]),
         g=>LinearMap([3 1 1 1; -1 -1 -1 -1; 0 2 0 0.0]),
         h=>LinearMap([1 4 -1; -1 1 0; 1 1 -1.0]),
         V=>LinearMapDom(4),
         W=>LinearMapDom(3))
F(ex) = functor((LinearMapDom, LinearMap), ex, generators=d)

Random.seed!(1) # Set seed to avoid sporadic test failures.
n = 4
m = 3
x = ones(Float64, n)
A = F(M)'*F(M)
b = A*x
x̂ᴰ = Matrix(A)\b

@test IterativeSolvers.zerox(F(M), b) == IterativeSolvers.zerox(Matrix(F(M)), b)
x̂ = gmres(A, b; maxiter=20)

b̂ = A*x̂
@test norm(b̂-b) < 1e-8

n = 32
M = plus(f,g)⋅h
M₄ = foldl(⊕, [M, M, M, M, M, M, M, M])
x = ones(Float64, n)
# A needs to be square and nonsingular
A = ( F(M₄)'*F(M₄) ) + UniformScaling(n)
b = A*x
x̂ᴰ = Matrix(A)\b

x̂, h = gmres(A, b; tol=1e-12, maxiter=160, log=true, verbose=false)

b̂ = A*x̂
@test norm(b̂-b) < 1e-8
@test norm(x̂-x)/norm(x) < 1e-8

Σ = svdl(A; k=10)[1]

# Eigensystem tests

λ, Q = powm(F(M)'*F(M))
@test norm((F(M)'*F(M))*Q - λ*Q) < 1e-3
λ, Q = powm(F(M⋅adjoint(M)))
@test norm(F(M⋅adjoint(M))*Q - λ*Q) < 1e-3

Σ, L = svdl(F(M))
@test all(Σ .>= 0)


λ, Q = powm(A)
@test norm(A*Q - λ*Q) < 1e-8

Σ, L = svdl(A)
@test all(Σ .>= 0)

M′ = ( M⊕id(V) ) + ( id(V)⊕M )
M₂ = ( M′⋅adjoint(M′) ) + id(V⊕V)
@test all(svd(Matrix(F(M₂))).S .> 1e-10)
b = ones(size(F(M₂), 1))
x̂ = gmres(F(M₂), b)
b̂ = F(M₂)*x̂
@test norm(b̂ .- 1) < 1e-12

#x₂ = vcat(x,-x)
#b₂= F(M₂)*x₂
#x̂₂ = gmres(F(M₂), b₂)
#b̂₂ = F(M₂)*x̂₂
#@test norm(b̂₂-b₂) < 1e-4
#@test norm(x̂₂-x₂) < 1e-4

# LinearOps instance
#-------------------

f, g = LinearOperator([0 1; 1 0]), LinearOperator([1 2 3; 4 5 6; 7 8 9])
h, k = LinearOperator([1 -1; -1 1; 0 1]), LinearOperator([1 1; 2 2; 3 3])

x, y = [2, 1], [7, 3, 5]
@test (f⋅f)*x == f*(f*x)
@test (f⋅h)*x == h*(f*x)
@test (f⊕g)*[x;y] == [f*x; g*y]
@test braid(dom(f),dom(g)) * [x;y] == [y;x]

@test mcopy(dom(f))*x == [x;x]
@test delete(dom(f))*x == []
@test plus(dom(f))*[x;x] == 2x
@test zero(dom(f))*Float64[] == zero(x)

@test (h+k)*x == h*x + k*x
@test scalar(dom(f),3)*x == 3*x
@test antipode(dom(f))*x == -1*x
@test adjoint(g)*y == g'*y

# LinearOps functor
#------------------

A, B = Ob(FreeLinearFunctions, :A, :B)

f, g  = Hom(:f, A, B), Hom(:g, A, B)
h, k  = Hom(:f, B, A), Hom(:g, B, A)

fop, gop = LinearOperator([0 1 -1; -1 1 0]), LinearOperator([1 2 3; 4 5 6])
hop, kop = LinearOperator([1 -1; -1 1; 0 1]), LinearOperator([1 1; 2 2; 3 3])

d = Dict(f=>fop, h=>hop, g => gop, k => kop)

F(ex)=functor((LinearOpDom, LinearOperator), ex, generators=d)

@test Matrix(F(compose(f,h))*[1 1; 2 3; 4 5]) == Matrix(hop*fop*[1 1; 2 3; 4 5])
@test Matrix(F(compose(g,k))*[1 1; 2 3; 4 5]) == Matrix(kop*gop*[1 1; 2 3; 4 5])

# Catlab evaluate
#----------------

A, B = Ob(FreeLinearFunctions, :A, :B)
f, g, h, k = Hom(:f, A, A), Hom(:g, B, B), Hom(:h, A, B), Hom(:k, A, B)
generators = Dict(
  A => 2, B => 3,
  f => [0 1; 1 0],
  g => [1 2 3; 4 5 6; 7 8 9],
  h => [1 -1; -1 1; 0 1],
  k => [1 1; 2 2; 3 3],
)
ev = (args...) -> evaluate(args...; generators=generators)

val = arg -> generators[arg]
x, y = [2, 1], [7, 3, 5]
@test ev(f, x) == val(f)*x

@test ev(f⋅f, x) == val(f)*(val(f)*x)
@test ev(f⋅h, x) == val(h)*(val(f)*x)
@test ev(f⊕g, x, y) == (val(f)*x, val(g)*y)

@test ev(plus(A), [1,3], [2,4]) == [3,7]
@test ev(zero(A)) == [0,0]
@test ev(h+k, x) == val(h)*x + val(k)*x
@test ev(scalar(A,3),x) == 3*x
@test ev(antipode(A),x) == -1*x

# Wiring diagrams
#################

A, B = Ob(FreeLinearFunctions, :A, :B)
f, g, h, k = Hom(:f, A, A), Hom(:g, B, B), Hom(:h, A, B), Hom(:k, A, B)

d = to_wiring_diagram(f⋅h⋅g)
@test nboxes(d) == 3
@test dom(d) == Ports([:A])
@test codom(d) == Ports([:B])

@present Mat(FreeLinearFunctions) begin
    X::Ob
    Y::Ob
    Z::Ob
    V::Ob
    W::Ob

    f::Hom(X,Y)
    g::Hom(Y,Z)
    h::Hom(Y⊕Z, V)
    fˣ::Hom(X,X)
    fʸ::Hom(Y,Y)
    fᶻ::Hom(Z,Z)
    fᵛ::Hom(V,V)
    fʷ::Hom(W,W)
end

@test_skip A = @program Mat (x::X,y::Y) begin
    v = h(f(x),g(y))
    return v
end

@test_skip codom(A) == generator(Mat, :V)

@test_skip A = @program Mat (x::X,y::Y) begin
    v = h(f(x),g(y))
    return fᵛ(v)
end

@test_skip codom(A) == generator(Mat, :V)

end
