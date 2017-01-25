using CompCat.Syntax
using Base.Test

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
