using Test

# 2-category
############

A, B, C, D = Ob(FreeCategory2, :A, :B, :C, :D)
f, g = [Hom(sym, A, B) for sym in [:f,:g]]
h, k = [Hom(sym, B, C) for sym in [:h,:k]]

# Domains and codomains
α, β = Hom2(:α, f, g), Hom2(:β, g, h)
@test dom(α) == f
@test codom(α) == g
@test dom(dom(α)) == A
@test codom(dom(α)) == B
@test dom(compose(α,β)) == f
@test codom(compose(α,β)) == h
@test_throws SyntaxDomainError composeH(α,β)

α, β = Hom2(:α, f, g), Hom2(:β, h, k)
@test dom(composeH(α,β)) == compose(f,h)
@test codom(composeH(α,β)) == compose(g,k)

# Infix notation (Unicode)
α, β = Hom2(:α, f, g), Hom2(:β, g, h)
@test unicode(compose(f,h)) == "f⋅h"
@test unicode(compose(α,β)) == "α⋅β"

α, β = Hom2(:α, f, g), Hom2(:β, h, k)
@test unicode(composeH(α,β)) == "α*β"

# Whiskering
α, β = Hom2(:α, f, g), Hom2(:β, h, k)
@test α*h == α*id(h)
@test f*β == id(f)*β

# Double category
#################

A, B, C, X, Y, Z = Ob(FreeDoubleCategory, :A, :B, :C, :X, :Y, :Z)
f, g, h = Hom(:f, A, X), Hom(:g, B, Y), Hom(:h, C, Z)
m, n, p, q = Pro(:m, A, B), Pro(:n, B, C), Pro(:p, X, Y), Pro(:q, Y, Z)
@test src(m) == A
@test tgt(m) == B

# Cell domains and codomains
α, β = Cell(:α, m, p, f, g), Cell(:β, n, q, g, h)
@test dom(α) == m
@test codom(α) == p
@test src(α) == f
@test tgt(α) == g

# External composition
αβ = pcompose(α, β)
@test α*β == αβ
@test dom(αβ) == pcompose(m, n)
@test codom(αβ) == pcompose(p, q)
@test src(αβ) == f
@test tgt(αβ) == h

# Monoidal double category
##########################

A, B, C, D, A′, B′, C′, D′ = Ob(FreeSymmetricMonoidalDoubleCategory,
                                :A, :B, :C, :D, :A′, :B′, :C′, :D′)
m, n, m′, n′ = Pro(:m,A,B), Pro(:n,C,D), Pro(:m′,A′,B′), Pro(:n′,C′,D′)
f, g, f′, g′ = Hom(:f,A,C), Hom(:g,B,D), Hom(:f′,A′,C′), Hom(:g′,B′,D′)
α, α′ = Cell(:α, m, n, f, g), Cell(:α′, m′, n′, f′, g′)

# Domains and codomains
@test src(m ⊗ n) == src(m) ⊗ src(n)
@test tgt(m ⊗ n) == tgt(m) ⊗ tgt(n)
@test dom(f ⊗ g) == dom(f) ⊗ dom(g)
@test codom(f ⊗ g) == codom(f) ⊗ codom(g)
@test src(α ⊗ α′) == src(α) ⊗ src(α′)
@test tgt(α ⊗ α′) == tgt(α) ⊗ tgt(α′)
@test dom(α ⊗ α′) == dom(α) ⊗ dom(α′)
@test codom(α ⊗ α′) == codom(α) ⊗ codom(α′)

@test dom(σ(A,B)) == A⊗B
@test codom(σ(A,B)) == B⊗A
@test dom(σ(m,n)) == m⊗n
@test codom(σ(m,n)) == n⊗m
@test src(σ(m,n)) == σ(A,C)
@test tgt(σ(m,n)) == σ(B,D)
