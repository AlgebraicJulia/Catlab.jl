module TestDoctrine

using Base.Test
using CompCat.Doctrine
using CompCat.Syntax

sexpr(expr::BaseExpr) = sprint(show_sexpr, expr)
unicode(expr::BaseExpr) = sprint(show_unicode, expr)
latex(expr::BaseExpr) = sprint(show_latex, expr)

# Category
##########

A, B = FreeCategory.ob(:A), FreeCategory.ob(:B)
f, g = FreeCategory.hom(:f, A, B), FreeCategory.hom(:g, B, A)

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
@test g∘f == compose(f,g)
@test f∘g∘f == compose(compose(f,g),f)

# String format
@test string(A) == "A"
@test string(f) == "f"
@test string(compose(f,g)) == "compose(f,g)"
@test string(compose(f,g,f)) == "compose(f,g,f)"

# S-expressions
@test sexpr(A) == ":A"
@test sexpr(f) == ":f"
@test sexpr(compose(f,g)) == "(compose :f :g)"
@test sexpr(compose(f,g,f)) == "(compose :f :g :f)"

# Infix notation (Unicode)
@test unicode(A) == "A"
@test unicode(f) == "f"
@test unicode(id(A)) == "id[A]"
@test unicode(compose(f,g)) == "f⋅g"

# Infix notation (LaTeX)
@test latex(A) == "A"
@test latex(f) == "f"
@test latex(id(A)) == "\\mathrm{id}_{A}"
@test latex(compose(f,g)) == "f \\cdot g"

# 2-category
############

Syntax = FreeCategory2
A, B, C, D = [ Syntax.ob(sym) for sym in [:A,:B,:C,:D] ]
f, g, F, G = [ Syntax.hom(sym, A, B) for sym in [:f,:g,:F,:G] ]
h, k, H, K = [ Syntax.hom(sym, B, C) for sym in [:h,:k,:H,:K] ]

# Domains and codomains
α, β = Syntax.hom2(:α, f, g), Syntax.hom2(:β, g, h)
@test dom(α) == f
@test codom(α) == g
@test dom(dom(α)) == A
@test codom(dom(α)) == B
@test dom(compose(α,β)) == f
@test codom(compose(α,β)) == h
@test_throws SyntaxDomainError compose2(α,β)

α, β = Syntax.hom2(:α, f, g), Syntax.hom2(:β, h, k)
@test dom(compose2(α,β)) == compose(f,h)
@test codom(compose2(α,β)) == compose(g,k)

# Infix notation (Unicode)
α, β = Syntax.hom2(:α, f, g), Syntax.hom2(:β, g, h)
@test unicode(compose(f,h)) == "f⋅h"
@test unicode(compose(α,β)) == "α⋅β"

α, β = Syntax.hom2(:α, f, g), Syntax.hom2(:β, h, k)
@test unicode(compose2(α,β)) == "α*β"

# Symmetric monoidal category
#############################

Syntax = FreeSymmetricMonoidalCategory
A, B = Syntax.ob(:A), Syntax.ob(:B)
f, g = Syntax.hom(:f, A, B), Syntax.hom(:g, B, A)

# Domains and codomains
@test dom(otimes(f,g)) == otimes(dom(f),dom(g))
@test codom(otimes(f,g)) == otimes(codom(f),codom(g))
@test dom(braid(A,B)) == otimes(A,B)
@test codom(braid(A,B)) == otimes(B,A)

# Associativity and unit
I = munit(Syntax.Ob)
@test otimes(A,I) == A
@test otimes(I,A) == A
@test otimes(otimes(A,B),A) == otimes(A,otimes(B,A))
@test otimes(otimes(f,g),f) == otimes(f,otimes(g,f))

# Extra syntax
@test otimes(f,f,f) == otimes(otimes(f,f),f)
@test A⊗B == otimes(A,B)
@test f⊗g == otimes(f,g)

# String format
@test string(otimes(f,g)) == "otimes(f,g)"
@test string(compose(otimes(f,f),otimes(g,g))) == "compose(otimes(f,f),otimes(g,g))"

# S-expressions
@test sexpr(I) == "(munit)"
@test sexpr(otimes(A,B)) == "(otimes :A :B)"
@test sexpr(otimes(f,g)) == "(otimes :f :g)"
@test sexpr(compose(otimes(f,f),otimes(g,g))) == "(compose (otimes :f :f) (otimes :g :g))"

# Infix notation (Unicode)
@test unicode(I) == "I"
@test unicode(otimes(A,B)) == "A⊗B"
@test unicode(otimes(f,g)) == "f⊗g"
@test unicode(compose(otimes(f,f),otimes(g,g))) == "(f⊗f)⋅(g⊗g)"
@test unicode(otimes(compose(f,g),compose(g,f))) == "(f⋅g)⊗(g⋅f)"

# Infix notation (LaTeX)
@test latex(I) == "I"
@test latex(otimes(A,B)) == "A \\otimes B"
@test latex(otimes(f,g)) == "f \\otimes g"
@test latex(compose(otimes(f,f),otimes(g,g))) == 
  "\\left(f \\otimes f\\right) \\cdot \\left(g \\otimes g\\right)"
@test latex(otimes(compose(f,g),compose(g,f))) == 
  "\\left(f \\cdot g\\right) \\otimes \\left(g \\cdot f\\right)"
@test latex(braid(A,B)) == "\\sigma_{A,B}"

# Cartesian category
####################

Syntax = FreeCartesianCategory
A, B = Syntax.ob(:A), Syntax.ob(:B)
f, g = Syntax.hom(:f, A, B), Syntax.hom(:g, B, A)

# Domains and codomains
@test dom(mcopy(A)) == A
@test codom(mcopy(A)) == otimes(A,A)
@test dom(delete(A)) == A
@test codom(delete(A)) == I

# Derived syntax
@test pair(f,f) == compose(mcopy(A), otimes(f,f))
@test proj1(A,B) == otimes(id(A), delete(B))
@test proj2(A,B) == otimes(delete(A), id(B))

# Infix notation (LaTeX)
@test latex(mcopy(A)) == "\\Delta_{A}"
@test latex(delete(A)) == "\\lozenge_{A}" 

# Cocartesian category
######################

Syntax = FreeCocartesianCategory
A, B = Syntax.ob(:A), Syntax.ob(:B)
f, g = Syntax.hom(:f, A, B), Syntax.hom(:g, B, A)

# Domains and codomains
@test dom(mmerge(A)) == otimes(A,A)
@test codom(mmerge(A)) == A
@test dom(create(A)) == I
@test codom(create(A)) == A

# Derived syntax
@test copair(f,f) == compose(otimes(f,f), mmerge(B))
@test in1(A,B) == otimes(id(A), create(B))
@test in2(A,B) == otimes(create(A), id(B))

# Infix notation (LaTeX)
@test latex(mmerge(A)) == "\\nabla_{A}"
@test latex(create(A)) == "\\square_{A}"

# Compact closed category
#########################

Syntax = FreeCompactClosedCategory
A, B = Syntax.ob(:A), Syntax.ob(:B)
f, g = Syntax.hom(:f, A, B), Syntax.hom(:g, B, A)

# Domains and codomains
@test dom(ev(A)) == otimes(A, dual(A))
@test codom(ev(A)) == I
@test dom(coev(A)) == I
@test codom(coev(A)) == otimes(dual(A), A)

# Infix notation (LaTeX)
@test latex(dual(A)) == "A^*"
@test latex(ev(A)) == "\\mathrm{ev}_{A}"
@test latex(coev(A)) == "\\mathrm{coev}_{A}"

# Dagger compact category
#########################

Syntax = FreeDaggerCompactCategory
A, B = Syntax.ob(:A), Syntax.ob(:B)
f, g = Syntax.hom(:f, A, B), Syntax.hom(:g, B, A)

# Domains and codomains
@test dom(dagger(f)) == B
@test codom(dagger(f)) == A

# Infix notation (LaTeX)
@test latex(dagger(f)) == "f^\\dagger"
@test latex(dagger(compose(f,g))) == "\\left(f \\cdot g\\right)^\\dagger"

end
