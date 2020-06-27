module TestFinRelations
using Test

using Catlab.Theories, Catlab.CategoricalAlgebra.FinRelations

# Category of finite ordinals and relations
###########################################

R = FinOrdRelation(Matrix{BoolRig}([true false true; false true false]))
S = FinOrdRelation(Matrix{BoolRig}([false true; true false]))

# Evaluation.
@test map(R, [1,3], [1,2]) == [true, false]
@test map(id(FinOrdRelOb(3)), [1,1], [1,2]) == [true, false]
@test map(FinOrdRelation((x,y) -> 2x == y, 3, 6), [1,1], [2,1]) == [true, false]

# Composition and identities.
@test dom(R) == FinOrdRelOb(3)
@test codom(R) == FinOrdRelOb(2)
@test compose(R,S) == FinOrdRelation(Matrix{BoolRig}([false true false; true false true]))
@test force(compose(id(dom(R)),R)) == R
@test force(compose(R,id(codom(R)))) == R

end
