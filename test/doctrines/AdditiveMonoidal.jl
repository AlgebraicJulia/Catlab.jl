using Test

# Symmetric monoidal category
#############################

A, B = Ob(FreeAdditiveSymmetricMonoidalCategory, :A, :B)
f, g = Hom(:f, A, B), Hom(:g, B, A)

# Domains and codomains
@test dom(oplus(f,g)) == oplus(dom(f),dom(g))
@test codom(oplus(f,g)) == oplus(codom(f),codom(g))
@test dom(braid(A,B)) == oplus(A,B)
@test codom(braid(A,B)) == oplus(B,A)
