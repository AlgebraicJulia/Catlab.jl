using Test

# Groupoid
##########

A, B, C = Ob(FreeGroupoid, :A), Ob(FreeGroupoid, :B), Ob(FreeGroupoid, :C)
f, g, h, k = Hom(:f, A, B), Hom(:g, B, C), Hom(:h, B, A), Hom(:k, C, B)

# Domains and codomains
@test dom(inverse(f)) == B
@test codom(inverse(f)) == A

# Associativity and unitality
@test compose(compose(f,g),k) == compose(f,compose(g,k))
@test compose(id(A), f) == f
@test compose(f, id(B)) == f

# Inverse laws
@test compose(f,inverse(f)) == id(A)
@test compose(inverse(f),f) == id(B)
@test compose(inverse(f),compose(f,g)) == g
@test compose(h,compose(inverse(h),g)) == g
@test compose(compose(f,g),inverse(g)) == f
@test compose(compose(k,inverse(f)),f) == k
@test compose(compose(f,inverse(k)),compose(k,inverse(f))) == id(A)

# Dsitributive property
@test inverse(compose(f,g)) == compose(inverse(g),inverse(f))

# Involution
@test inverse(inverse(f)) == f

# Identity self-inverse
@test inverse(id(A)) == id(A)
