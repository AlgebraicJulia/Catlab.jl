using CompCat.Syntax
using Base.Test

A, B = ob(:A), ob(:B)
f = mor(:f, A, B)
g = mor(:f, B, A)

@test dom(compose(f,g)) == A
@test codom(compose(f,g)) == A
