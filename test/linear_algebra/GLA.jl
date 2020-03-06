module TestGraphicalLinearAlgebra
using Test

using IterativeSolvers

using Catlab, Catlab.Doctrines, Catlab.WiringDiagrams, Catlab.Programs
using Catlab.LinearAlgebra.GraphicalLinearAlgebra
import LinearAlgebra: norm

import LinearMaps: BlockDiagonalMap

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
@test mplus(dom(f))*[x;x] == 2x
@test mzero(dom(f))*Float64[] == zero(x)

@test (h+k)*x == h*x + k*x
@test scalar(dom(f),3)*x == 3*x
@test antipode(dom(f))*x == -1*x
@test adjoint(g)*y == g'*y

# GMRES with LinearMaps
#----------------------

A, B = Ob(FreeLinearFunctions, :A, :B)
f, g, h = Hom(:f, A, B), Hom(:g, A, B), Hom(:h, B, B)

M = plus(f,g)⋅h
# M = plus(f,g)

M′ = M⊕id(A) + id(A)⊕M
#M₂ = M′⋅M′

d = Dict(f=>LinearMap([1 1 1 1; 2 2 2 2; 3 3 3 3.0]),
         g=>LinearMap([1 1 1 1; -1 -1 -1 -1; 0 0 0 0.0]),
         h=>LinearMap([1 0 -1; -1 1 0; 1 1 -1.0]))
F(ex) = functor((LinearMapDom, LinearMap), ex, generators=d)


n = 4
m = 3
x = ones(Float64, n)
b = F(M)*x
x̂ᴰ = Matrix(F(M))\b

# x̂ = gmres(F(M), b)
# b̂ = F(M)*x̂
@test_skip norm(b̂-b) < 1e-8
@test_skip norm(x̂-x) < 1e-8

# Eigensystem tests
A = BlockDiagonalMap(LinearMap(identity, 3), LinearMap(identity, 3))
@test norm( (A+A)*gmres(A+A, ones(6)) .- ones(6) ) < 1e-4

λ, V = powm(F(M)'*F(M))
norm((F(M)'*F(M))*V - λ*V) < 1e-4
λ, V = powm(F(M⋅adjoint(M)))
norm(F(M⋅adjoint(M))*V - λ*V) < 1e-4

Σ, L = svdl(F(M))
@test all(Σ .>= 0)



#x₂ = vcat(x,-x)
#b₂= F(M₂)*x₂
#x̂₂ = gmres(F(M₂), b₂)
#b̂₂ = F(M₂)*x̂₂
#@test norm(b̂₂-b₂) < 1e-4
#@test norm(x̂₂-x₂) < 1e-4

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

@test ev(mplus(A), [1,3], [2,4]) == [3,7]
@test ev(mzero(A)) == [0,0]
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
