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
@test f∘g == compose(f,g)
@test f∘g∘f == compose(compose(f,g),f)

# Pretty-print
function sexpr(expr)
  buf = IOBuffer(); show_sexpr(buf, expr); takebuf_string(buf)
end

@test sexpr(A) == ":A"
@test sexpr(f) == ":f"
@test sexpr(compose(f,g)) == "(compose :f :g)"
@test sexpr(compose(f,g,f)) == "(compose :f :g :f)"

function infix(expr)
  buf = IOBuffer(); pprint(buf, expr); takebuf_string(buf)
end

@test infix(A) == "A"
@test infix(f) == "f : A → B"
@test infix(id(A)) == "id[A] : A → A"
@test infix(compose(f,g)) == "f g : A → A"

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
@test sexpr(otimes(A,B)) == "(otimes :A :B)"
@test sexpr(otimes(f,g)) == "(otimes :f :g)"
@test sexpr(compose(otimes(f,f),otimes(g,g))) == "(compose (otimes :f :f) (otimes :g :g))"

@test infix(otimes(A,B)) == "A⊗B"
@test infix(otimes(f,g)) == "f⊗g : A⊗B → B⊗A"
@test infix(mor_expr(:f, I, A)) == "f : I → A"
@test infix(compose(otimes(f,f),otimes(g,g))) == "(f⊗f) (g⊗g) : A⊗A → A⊗A"
@test infix(otimes(compose(f,g),compose(g,f))) == "(f g)⊗(g f) : A⊗B → A⊗B"
