using Test

# Category
##########

A, B = Ob(FreeCategory, :A), Ob(FreeCategory, :B)
f, g = Hom(:f, A, B), Hom(:g, B, A)

# Expression types
@test isa(A, FreeCategory.Ob) && isa(f, FreeCategory.Hom)
@test isa(A, ObExpr) && isa(f, HomExpr)
@test isa(A, CategoryExpr) && isa(f, CategoryExpr)

# Domains and codomains
@test dom(f) == A
@test codom(f) == B
@test dom(compose(f,g)) == A
@test codom(compose(f,g)) == A
@test_throws SyntaxDomainError compose(f,f)

# Associativity
@test compose(compose(f,g),f) == compose(f,compose(g,f))

# Extra syntax
@test compose(f,g,f) == compose(compose(f,g),f)
@test compose([f,g,f]) == compose(compose(f,g),f)
@test f⋅g == compose(f,g)
@test f⋅g⋅f⋅g == compose(f,g,f,g)

# String format
@test string(A) == "A"
@test string(f) == "f"
@test string(compose(f,g)) == "compose(f,g)"
@test string(compose(f,g,f)) == "compose(f,g,f)"
@test string(Ob(FreeCategory, nothing)) != ""

# S-expressions
@test sexpr(A) == ":A"
@test sexpr(f) == ":f"
@test sexpr(compose(f,g)) == "(compose :f :g)"
@test sexpr(compose(f,g,f)) == "(compose :f :g :f)"

# Infix notation (Unicode)
@test unicode(A) == "A"
@test unicode(f) == "f"
@test unicode(id(A)) == "id{A}"
@test unicode(compose(f,g)) == "f⋅g"

# Infix notation (LaTeX)
@test latex(A) == "A"
@test latex(f) == "f"
@test latex(id(A)) == "\\mathrm{id}_{A}"
@test latex(compose(f,g)) == "f \\cdot g"

@test latex(Ob(FreeCategory, "x")) == "x"
@test latex(Ob(FreeCategory, "sin")) == "\\mathrm{sin}"
@test latex(Ob(FreeCategory, "\\alpha")) == "\\alpha"

# 2-category
############

A, B, C, D = Ob(FreeCategory2, :A, :B, :C, :D)
f, g, F, G = [ Hom(sym, A, B) for sym in [:f,:g,:F,:G] ]
h, k, H, K = [ Hom(sym, B, C) for sym in [:h,:k,:H,:K] ]

# Domains and codomains
α, β = Hom2(:α, f, g), Hom2(:β, g, h)
@test dom(α) == f
@test codom(α) == g
@test dom(dom(α)) == A
@test codom(dom(α)) == B
@test dom(compose(α,β)) == f
@test codom(compose(α,β)) == h
@test_throws SyntaxDomainError compose2(α,β)

α, β = Hom2(:α, f, g), Hom2(:β, h, k)
@test dom(compose2(α,β)) == compose(f,h)
@test codom(compose2(α,β)) == compose(g,k)

# Infix notation (Unicode)
α, β = Hom2(:α, f, g), Hom2(:β, g, h)
@test unicode(compose(f,h)) == "f⋅h"
@test unicode(compose(α,β)) == "α⋅β"

α, β = Hom2(:α, f, g), Hom2(:β, h, k)
@test unicode(compose2(α,β)) == "α*β"

# Incompatible theories
@test_throws MethodError Hom(:f, Ob(FreeCategory, :A), Ob(FreeCategory2, :B))
f = Hom(:f, Ob(FreeCategory, :A), Ob(FreeCategory, :B))
g = Hom(:g, Ob(FreeCategory2, :B), Ob(FreeCategory2, :C))
@test_throws MethodError compose(f,g)


# Double Category
#################

A, B, C, D, X, Y = [Ob(FreeDoubleCategory, x) for x in [:A, :B, :C, :D, :X, :Y]]
@show typeof(A), typeof(X)
f, g, h, k = HomH(:f, A, X), HomH(:g, B, Y), HomH(h, X, C), HomH(:k, Y, D)
l, r, rr = HomV(:ϕ, A, B), HomV(:r, X, Y), HomV(:rr, C, D)
α, β = Hom2(:α, f, g, l, r), Hom2(:β, h, k, r, rr)
@test composeH(α, β) == α⋅β
αβ = composeH(α, β)
#@test top(αβ) == composeH(f, h)
#@test bottom(αβ) == composeH(g, k)