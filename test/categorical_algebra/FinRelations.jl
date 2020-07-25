module TestFinRelations
using Test

using Catlab.Theories, Catlab.CategoricalAlgebra.FinRelations
using Catlab.CategoricalAlgebra.Matrices: MatrixDom

# Category of finite ordinals and relations
###########################################

R = FinRelation(Matrix{BoolRig}([true false true; false true false]))
@test dom(R) == FinRel(3)
@test codom(R) == FinRel(2)

# Evaluation.
@test map(R, [1,3], [1,2]) == [true, false]
@test map(id(FinRel(3)), [1,1], [1,2]) == [true, false]
@test map(FinRelation((x,y) -> 2x == y, 3, 6), [1,1], [2,1]) == [true, false]

# Compatibility of function and matrix representations.
R = FinRelation((x,y) -> x == y || x == 2y || x == 3y, 10, 5)
S = FinRelation((x,y) -> (x+y) % 2 == 0, 5, 10)
A, B = dom(R), dom(S)
m, n = length(A), length(B)
R_mat, S_mat = force(R), force(S)
A_mat, B_mat = MatrixDom{Matrix{BoolRig}}(m), MatrixDom{Matrix{BoolRig}}(n)

@test force(R ⋅ S) == R_mat ⋅ S_mat
@test force(R ⋅ id(codom(R))) == R_mat
@test force(id(dom(R)) ⋅ R) == R_mat
@test force(dagger(R)) == dagger(R_mat)

@test force(R ⊗ S) == R_mat ⊗ S_mat
@test force(braid(A, B)) == FinRelation(braid(A_mat, B_mat))

@test force(R ⊕ S) == R_mat ⊕ S_mat
@test force(swap(A, B)) == FinRelation(swap(A_mat, B_mat))

S = FinRelation((x,y) -> (x+y) % 2 == 0, 10, 5)
S_mat = force(S)
@test force(meet(R, S)) == meet(R_mat, S_mat)
@test force(join(R, S)) == join(R_mat, S_mat)
@test force(mcopy(dom(R))⋅(R⊗S)⋅mmerge(codom(R))) == meet(R_mat, S_mat)
@test force(coplus(dom(R))⋅(R⊕S)⋅plus(codom(R))) == join(R_mat, S_mat)

@test force(top(A, B)) == FinRelation(ones(BoolRig, n, m))
@test force(bottom(A, B)) == FinRelation(zeros(BoolRig, n, m))
@test force(delete(A)⋅create(B)) == FinRelation(ones(BoolRig, n, m))
@test force(cozero(A)⋅zero(B)) == FinRelation(zeros(BoolRig, n, m))

@test force(pair(R, S)) == pair(R_mat, S_mat)
@test force(copair(R, S)) == copair(R_mat, S_mat)

end
