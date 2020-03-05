module TestGraphicalLinearAlgebra
using Test

using Catlab.LinearAlgebra

# Doctrines
###########

A, B = Ob(FreeLinearMaps, :A, :B)
f, g = Hom(:f, A, B), Hom(:g, A, B)

# Domains and codomains
@test dom(plus(f,g)) == A
@test codom(plus(f,g)) == B

# Unicode syntax
@test f+g == plus(f,g)

# Evaluation
############

A, B = Ob(FreeLinearMaps, :A, :B)
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

end
