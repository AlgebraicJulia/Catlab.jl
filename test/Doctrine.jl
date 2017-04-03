module TestDoctrine

using Base.Test
using CompCat.Doctrine
using CompCat.Syntax

sexpr(expr::BaseExpr) = sprint(show_sexpr, expr)

# Category
##########

A, B = FreeCategory.ob(:A), FreeCategory.ob(:B)
f, g = FreeCategory.hom(:f, A, B), FreeCategory.hom(:g, B, A)

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

# S-expressions
@test sexpr(A) == ":A"
@test sexpr(f) == ":f"
@test sexpr(compose(f,g)) == "(compose :f :g)"
@test sexpr(compose(f,g,f)) == "(compose :f :g :f)"

# 2-category
############

A, B = FreeCategory2.ob(:A), FreeCategory2.ob(:B)
f, g, h = [ FreeCategory2.hom(sym, A, B) for sym in [:f,:g,:h] ]
α, β = FreeCategory2.hom2(:α, f, g), FreeCategory2.hom2(:β, g, h)

# Domains and codomains
@test dom(α) == f
@test codom(α) == g
@test dom(dom(α)) == A
@test codom(dom(α)) == B
@test dom(compose(α,β)) == f
@test codom(compose(α,β)) == h

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

# S-expressions
@test sexpr(I) == "(munit)"
@test sexpr(otimes(A,B)) == "(otimes :A :B)"
@test sexpr(otimes(f,g)) == "(otimes :f :g)"
@test sexpr(compose(otimes(f,f),otimes(g,g))) == "(compose (otimes :f :f) (otimes :g :g))"

# Cartesian category
####################

Syntax = FreeCartesianCategory
A, B = Syntax.ob(:A), Syntax.ob(:B)
f, g = Syntax.hom(:f, A, B), Syntax.hom(:g, B, A)

@test dom(mcopy(A)) == A
@test codom(mcopy(A)) == otimes(A,A)
@test dom(delete(A)) == A
@test codom(delete(A)) == I

# Cocartesian category
######################

Syntax = FreeCocartesianCategory
A, B = Syntax.ob(:A), Syntax.ob(:B)
f, g = Syntax.hom(:f, A, B), Syntax.hom(:g, B, A)

@test dom(mmerge(A)) == otimes(A,A)
@test codom(mmerge(A)) == A
@test dom(create(A)) == I
@test codom(create(A)) == A

# Compact closed category
#########################

Syntax = FreeCompactClosedCategory
A, B = Syntax.ob(:A), Syntax.ob(:B)
f, g = Syntax.hom(:f, A, B), Syntax.hom(:g, B, A)

@test dom(ev(A)) == otimes(A, dual(A))
@test codom(ev(A)) == I

@test dom(coev(A)) == I
@test codom(coev(A)) == otimes(dual(A), A)

# Dagger compact category
#########################

Syntax = FreeDaggerCompactCategory
A, B = Syntax.ob(:A), Syntax.ob(:B)
f, g = Syntax.hom(:f, A, B), Syntax.hom(:g, B, A)

@test dom(dagger(f)) == B
@test codom(dagger(f)) == A

# 
# # Infix (Unicode)
# infix(expr::BaseExpr) = sprint(show_infix, expr)
# 
# @test infix(A) == "A"
# @test infix(f) == "f"
# @test infix(id(A)) == "id[A]"
# @test infix(compose(f,g)) == "f g"
# 
# @test infix(I) == "I"
# @test infix(otimes(A,B)) == "A⊗B"
# @test infix(otimes(f,g)) == "f⊗g"
# @test infix(compose(otimes(f,f),otimes(g,g))) == "(f⊗f) (g⊗g)"
# @test infix(otimes(compose(f,g),compose(g,f))) == "(f g)⊗(g f)"
# 
# @test infix(braid(A,B)) == "braid[A,B]"
# @test infix(mmerge(A)) == "merge[A]"
# @test infix(mcopy(A)) == "copy[A]"
# @test infix(compose(mcopy(A), otimes(f,f))) == "copy[A] (f⊗f)"
# 
# @test infix(dagger(f)) == "dagger[f]"
# 
# # Infix (LaTeX)
# latex(expr::BaseExpr) = sprint(show_latex, expr)
# 
# @test latex(A) == "A"
# @test latex(f) == "f"
# @test latex(id(A)) == "\\mathrm{id}_{A}"
# @test latex(compose(f,g)) == "f g"
# 
# @test latex(I) == "I"
# @test latex(otimes(A,B)) == "A \\otimes B"
# @test latex(otimes(f,g)) == "f \\otimes g"
# @test latex(compose(otimes(f,f),otimes(g,g))) == 
#   "\\left(f \\otimes f\\right) \\left(g \\otimes g\\right)"
# @test latex(otimes(compose(f,g),compose(g,f))) == 
#   "\\left(f g\\right) \\otimes \\left(g f\\right)"
# 
# @test latex(braid(A,B)) == "\\sigma_{A,B}"
# 
# @test latex(mcopy(A)) == "\\Delta_{A}"
# @test latex(mmerge(A)) == "\\nabla_{A}"
# @test latex(create(A)) == "i_{A}"
# @test latex(delete(A)) == "e_{A}"
# 
# @test latex(dual(A)) == "A^{*}"
# @test latex(ev(A)) == "\\mathrm{ev}_{A}"
# @test latex(coev(A)) == "\\mathrm{coev}_{A}"
# 
# @test latex(dagger(f)) == "f^{\\dagger}"
# @test latex(dagger(compose(f,g))) == "\\left(f g\\right)^{\\dagger}"

end
