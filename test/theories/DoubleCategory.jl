using Test

# Double Category
#################

A, B, C, D, X, Y = Ob(FreeDoubleCategory, :A, :B, :C, :D, :X, :Y)
f, g, h, k = HomH(:f, A, X), HomH(:g, B, Y), HomH(:h, X, C), HomH(:k, Y, D)
l, r, rr = HomV(:ϕ, A, B), HomV(:r, X, Y), HomV(:rr, C, D)
α, β = Hom2(:α, f, g, l, r), Hom2(:β, h, k, r, rr)
@test composeH(α, β) == α⋆β
αβ = composeH(α, β)
@test top(αβ) == composeH(f, h)
@test bottom(αβ) == composeH(g, k)

# Symmetric monoidal double category
#############################

A, B, C, D = Ob(FreeSymmetricMonoidalDoubleCategory, :A, :B, :C, :D)
E, F, G, H = Ob(FreeSymmetricMonoidalDoubleCategory, :E, :F, :G, :H)
t, b, l, r = HomH(:t, A, B), HomH(:b, C, D), HomV(:l, A, C), HomV(:r, B, D)
t′, b′, l′, r′ = HomH(:t′, E, F), HomH(:b′, G, H), HomV(:l′, E, G), HomV(:r′, F, H)
s = Hom2(:s, t, b, l, r)
s′ = Hom2(:s′, t′, b′, l′, r′)

# Domains and codomains
@test dom(otimes(t,b)) == otimes(dom(t),dom(b))
@test codom(otimes(t,b)) == otimes(codom(t),codom(b))
@test dom(otimes(l,r)) == otimes(dom(l),dom(r))
@test codom(otimes(l,r)) == otimes(codom(l),codom(r))
@test top(otimes(s,s′)) == otimes(top(s),top(s′))
@test bottom(otimes(s,s′)) == otimes(bottom(s),bottom(s′))

@test dom(braidV(A,B)) == otimes(A,B)
@test codom(braidV(A,B)) == otimes(B,A)
@test top(braidH(t,b)) == otimes(t,b)
@test bottom(braidH(t,b)) == otimes(b,t)
@test left(braidH(t,b)) == braidV(A,C)
@test right(braidH(t,b)) == braidV(B,D)
@test σV(A, B) == braidV(A,B)
@test σH(t, b) == braidH(t,b)

# Associativity and unit
I = munit(FreeSymmetricMonoidalDoubleCategory.Ob)
@test otimes(A,I) == A
@test otimes(I,A) == A
@test otimes(otimes(A,B),A) == otimes(A,otimes(B,A))
@test otimes(otimes(t,b),t) == otimes(t,otimes(b,t))
