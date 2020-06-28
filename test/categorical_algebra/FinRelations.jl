module TestFinRelations
using Test

using Catlab.Theories, Catlab.CategoricalAlgebra.FinRelations
using Catlab.CategoricalAlgebra.Matrices: MatrixDom

# Category of finite ordinals and relations
###########################################

R = FinOrdRelation(Matrix{BoolRig}([true false true; false true false]))
@test dom(R) == FinOrdRelOb(3)
@test codom(R) == FinOrdRelOb(2)

# Evaluation.
@test map(R, [1,3], [1,2]) == [true, false]
@test map(id(FinOrdRelOb(3)), [1,1], [1,2]) == [true, false]
@test map(FinOrdRelation((x,y) -> 2x == y, 3, 6), [1,1], [2,1]) == [true, false]

# Compatibility of function and matrix representations.
R = FinOrdRelation((x,y) -> x == y || x == 2y || x == 3y, 10, 5)
S = FinOrdRelation((x,y) -> (x+y) % 2 == 0, 5, 10)
A, B = dom(R), dom(S)
R_mat, S_mat = force(R), force(S)
A_mat, B_mat = MatrixDom{Matrix{BoolRig}}(A.n), MatrixDom{Matrix{BoolRig}}(B.n)

@test force(R ⋅ S) == R_mat ⋅ S_mat
@test force(R ⋅ id(codom(R))) == R_mat
@test force(id(dom(R)) ⋅ R) == R_mat

@test force(R ⊗ S) == R_mat ⊗ S_mat
@test force(braid(A, B)) == FinOrdRelation(braid(A_mat, B_mat))

end
