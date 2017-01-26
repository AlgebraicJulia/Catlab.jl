using CompCat.Syntax
using Base.Test

# Category
##########

# Equality of equivalent generator instances
@test ob(:A) == ob(:A)
@test mor(:f, ob(:A), ob(:B)) == mor(:f, ob(:A), ob(:B))

# Domains and codomains
A, B = ob(:A), ob(:B)
f = mor(:f, A, B)
g = mor(:f, B, A)

@test dom(f) == A
@test codom(f) == B
@test dom(compose(f,g)) == A
@test codom(compose(f,g)) == A
@test_throws Exception compose(f,f)

# Extra syntax
@test compose(f,g,f) == compose(compose(f,g),f)
@test f∘g == compose(f,g)
@test f∘g∘f == compose(compose(f,g),f)

# Monoidal category
###################

I = munit(A)
@test otimes(A,I) == A
@test otimes(I,A) == A
@test otimes(otimes(A,B),A) == otimes(A,B,A)
@test otimes(A,otimes(B,A)) == otimes(A,B,A)

@test dom(otimes(f,g)) == otimes(dom(f),dom(g))
@test dom(otimes(f,f,f)) == otimes(dom(f),dom(f),dom(f))

# Extra syntax
@test A⊗B == otimes(A,B)
@test f⊗g == otimes(f,g)
