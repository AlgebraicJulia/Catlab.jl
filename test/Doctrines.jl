module TestDoctrines

using Test
using Catlab.Doctrines
using Catlab.Syntax

sexpr(expr::GATExpr) = sprint(show_sexpr, expr)
unicode(expr::GATExpr) = sprint(show_unicode, expr)
latex(expr::GATExpr) = sprint(show_latex, expr)

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
@test g∘f == compose(f,g)
@test g∘f∘g∘f == compose(f,g,f,g)

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

# Incompatible doctrines
@test_throws MethodError Hom(:f, Ob(FreeCategory, :A), Ob(FreeCategory2, :B))
f = Hom(:f, Ob(FreeCategory, :A), Ob(FreeCategory, :B))
g = Hom(:g, Ob(FreeCategory2, :B), Ob(FreeCategory2, :C))
@test_throws MethodError compose(f,g)

# Symmetric monoidal category
#############################

A, B = Ob(FreeSymmetricMonoidalCategory, :A, :B)
f, g = Hom(:f, A, B), Hom(:g, B, A)

# Domains and codomains
@test dom(otimes(f,g)) == otimes(dom(f),dom(g))
@test codom(otimes(f,g)) == otimes(codom(f),codom(g))
@test dom(braid(A,B)) == otimes(A,B)
@test codom(braid(A,B)) == otimes(B,A)

# Associativity and unit
I = munit(FreeSymmetricMonoidalCategory.Ob)
@test otimes(A,I) == A
@test otimes(I,A) == A
@test otimes(otimes(A,B),A) == otimes(A,otimes(B,A))
@test otimes(otimes(f,g),f) == otimes(f,otimes(g,f))

# Extra syntax
@test otimes(A,B,A) == otimes(otimes(A,B),A)
@test otimes([A,B,A]) == otimes(otimes(A,B),A)
@test otimes(f,f,f) == otimes(otimes(f,f),f)
@test otimes([f,f,f]) == otimes(otimes(f,f),f)
@test otimes(FreeSymmetricMonoidalCategory.Ob[]) == I
@test_throws MethodError otimes([])
@test A⊗B == otimes(A,B)
@test f⊗g == otimes(f,g)
@test A⊗B⊗A == otimes(A,B,A)

# Extra functions
@test collect(A) == [A]
@test collect(otimes(A,B)) == [A,B]
@test collect(I) == []
@test typeof(collect(I)) == Vector{FreeSymmetricMonoidalCategory.Ob}
@test ndims(A) == 1
@test ndims(otimes(A,B)) == 2
@test ndims(I) == 0

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

A, B = Ob(FreeCartesianCategory, :A, :B)
f, g = Hom(:f, A, B), Hom(:g, B, A)

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

A, B = Ob(FreeCocartesianCategory, :A, :B)
f, g = Hom(:f, A, B), Hom(:g, B, A)

# Domains and codomains
@test dom(mmerge(A)) == otimes(A,A)
@test codom(mmerge(A)) == A
@test dom(create(A)) == I
@test codom(create(A)) == A

# Derived syntax
@test copair(f,f) == compose(otimes(f,f), mmerge(B))
@test incl1(A,B) == otimes(id(A), create(B))
@test incl2(A,B) == otimes(create(A), id(B))

# Infix notation (LaTeX)
@test latex(mmerge(A)) == "\\nabla_{A}"
@test latex(create(A)) == "\\square_{A}"

# Cartesian closed category
###########################

A, B, C = Ob(FreeCartesianClosedCategory, :A, :B, :C)
f = Hom(:f, otimes(A,B), C)

# Domains and codomains
@test dom(ev(A,B)) == otimes(hom(A,B),A)
@test codom(ev(A,B)) == B
@test dom(curry(A,B,f)) == A
@test codom(curry(A,B,f)) == hom(B,C)

# Infix notation (LaTeX)
@test latex(hom(A,B)) == "B^{A}"
@test latex(ev(A,B)) == "\\mathrm{eval}_{A,B}"
@test latex(curry(A,B,f)) == "\\lambda f"

# Compact closed category
#########################

A, B, C = Ob(FreeCompactClosedCategory, :A, :B, :C)
I = munit(FreeCompactClosedCategory.Ob)
f = Hom(:f, otimes(A,B), C)

# Duals
@test dual(otimes(A,B)) == otimes(dual(B),dual(A))
@test dual(I) == I
@test dual(dual(A)) == A

# Domains and codomains
@test dom(dunit(A)) == I
@test codom(dunit(A)) == otimes(dual(A), A)
@test dom(dcounit(A)) == otimes(A, dual(A))
@test codom(dcounit(A)) == I

@test dom(ev(A,B)) == otimes(hom(A,B),A)
@test codom(ev(A,B)) == B
@test dom(curry(A,B,f)) == A
@test codom(curry(A,B,f)) == hom(B,C)

# Infix notation (LaTeX)
@test latex(dual(A)) == "A^*"
@test latex(dunit(A)) == "\\eta_{A}"
@test latex(dcounit(A)) == "\\varepsilon_{A}"

# Dagger category
#################

A, B = Ob(FreeDaggerCategory, :A, :B)
f, g = Hom(:f, A, B), Hom(:g, B, A)

# Domains and codomains
@test dom(dagger(f)) == B
@test codom(dagger(f)) == A

# Dagger
@test dagger(compose(f,g)) == compose(dagger(g),dagger(f))
@test dagger(id(A)) == id(A)
@test dagger(dagger(f)) == f

# Infix notation (LaTeX)
@test latex(dagger(f)) == "f^\\dagger"
#@test latex(dagger(compose(f,g))) == "\\left(f \\cdot g\\right)^\\dagger"

# Dagger compact category
#########################

A, B = Ob(FreeDaggerCompactCategory, :A, :B)
f, g = Hom(:f, A, B), Hom(:g, B, A)

# Dagger
@test dagger(compose(f,g)) == compose(dagger(g),dagger(f))
@test dagger(id(A)) == id(A)
@test dagger(dagger(f)) == f
@test dagger(otimes(f,g)) == otimes(dagger(f),dagger(g))
@test (dagger(otimes(compose(f,g),compose(g,f))) == 
       otimes(compose(dagger(g),dagger(f)),compose(dagger(f),dagger(g))))

end
