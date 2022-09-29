using Test

# Groupoid
##########

A, B, C = Ob(FreeGroupoid, :A), Ob(FreeGroupoid, :B), Ob(FreeGroupoid, :C)
f, g, h, k = Hom(:f, A, B), Hom(:g, B, C), Hom(:h, B, A), Hom(:k, C, B)

# Domains and codomains
@test dom(inv(f)) == B
@test codom(inv(f)) == A

# Associativity and unitality
@test compose(compose(f,g),k) == compose(f,compose(g,k))
@test compose(id(A), f) == f
@test compose(f, id(B)) == f

# Inverse laws
@test compose(f,inv(f)) == id(A)
@test compose(inv(f),f) == id(B)
@test compose(inv(f),compose(f,g)) == g
@test compose(h,compose(inv(h),g)) == g
@test compose(compose(f,g),inv(g)) == f
@test compose(compose(k,inv(f)),f) == k
@test compose(compose(f,inv(k)),compose(k,inv(f))) == id(A)

# Dsitributive property
@test inv(compose(f,g)) == compose(inv(g),inv(f))

# Involution
@test inv(inv(f)) == f

# Identity self-inv
@test inv(id(A)) == id(A)
