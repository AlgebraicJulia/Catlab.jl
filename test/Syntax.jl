using CompCat.Syntax
using Base.Test

# Generators
A, B = ob_expr(:A), ob_expr(:B)
f = mor_expr(:f, A, B)
g = mor_expr(:g, B, A)

# Equality of equivalent generators
@test ob_expr(:A) == ob_expr(:A)
@test mor_expr(:f, ob_expr(:A), ob_expr(:B)) == mor_expr(:f, ob_expr(:A), ob_expr(:B))

# Category
##########

# Domains and codomains
@test dom(f) == A
@test codom(f) == B
@test dom(compose(f,g)) == A
@test codom(compose(f,g)) == A
@test_throws Exception compose(f,f)

# Associativity
@test compose(compose(f,g),f) == compose(f,compose(g,f))

# Extra syntax
@test compose(f,g,f) == compose(compose(f,g),f)
@test g∘f == compose(f,g)
@test f∘g∘f == compose(compose(f,g),f)

# Monoidal category
###################

# Domains and codomains
@test dom(otimes(f,g)) == otimes(dom(f),dom(g))
@test codom(otimes(f,g)) == otimes(codom(f),codom(g))

# Associativity and unit
I = munit(A)
@test otimes(A,I) == A
@test otimes(I,A) == A
@test otimes(otimes(A,B),A) == otimes(A,otimes(B,A))
@test otimes(otimes(f,g),f) == otimes(f,otimes(g,f))

# Extra syntax
@test otimes(f,f,f) == otimes(otimes(f,f),f)
@test A⊗B == otimes(A,B)
@test f⊗g == otimes(f,g)

# Pretty-print
##############

# S-expressions
sexpr(expr::BaseExpr) = sprint(show_sexpr, expr)

@test sexpr(A) == ":A"
@test sexpr(f) == ":f"
@test sexpr(compose(f,g)) == "(compose :f :g)"
@test sexpr(compose(f,g,f)) == "(compose :f :g :f)"

@test sexpr(I) == "(unit)"
@test sexpr(otimes(A,B)) == "(otimes :A :B)"
@test sexpr(otimes(f,g)) == "(otimes :f :g)"
@test sexpr(compose(otimes(f,f),otimes(g,g))) == "(compose (otimes :f :f) (otimes :g :g))"

# Infix (Unicode)
infix(expr::BaseExpr) = sprint(show_infix, expr)

@test infix(A) == "A"
@test infix(f) == "f"
@test infix(id(A)) == "id[A]"
@test infix(compose(f,g)) == "f g"

@test infix(I) == "I"
@test infix(otimes(A,B)) == "A⊗B"
@test infix(otimes(f,g)) == "f⊗g"
@test infix(compose(otimes(f,f),otimes(g,g))) == "(f⊗f) (g⊗g)"
@test infix(otimes(compose(f,g),compose(g,f))) == "(f g)⊗(g f)"

# Infix (LaTeX)
latex(expr::BaseExpr) = sprint(show_latex, expr)

@test latex(A) == "A"
@test latex(f) == "f"
@test latex(id(A)) == "\\mathrm{id}_{A}"
@test latex(compose(f,g)) == "f g"

@test latex(I) == "I"
@test latex(otimes(A,B)) == "A \\otimes B"
@test latex(otimes(f,g)) == "f \\otimes g"
@test latex(compose(otimes(f,f),otimes(g,g))) == 
  "\\left(f \\otimes f\\right) \\left(g \\otimes g\\right)"
@test latex(otimes(compose(f,g),compose(g,f))) == 
  "\\left(f g\\right) \\otimes \\left(g f\\right)"
