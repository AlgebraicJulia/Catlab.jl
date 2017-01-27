using CompCat.Syntax
using Base.Test

# Category
##########

A, B = ob(:A), ob(:B)
f = mor(:f, A, B)
g = mor(:g, B, A)

# Equality of equivalent generator instances
@test ob(:A) == ob(:A)
@test mor(:f, ob(:A), ob(:B)) == mor(:f, ob(:A), ob(:B))

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
@test as_sexpr(A) == ":A"
@test as_sexpr(f) == ":f"
@test as_sexpr(compose(f,g)) == "(compose :f :g)"
@test as_sexpr(compose(f,g,f)) == "(compose :f :g :f)"

@test as_infix(A) == "A"
@test as_infix(f) == "f : A → B"
@test as_infix(id(A)) == "id[A] : A → A"
@test as_infix(compose(f,g)) == "f g : A → A"

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
@test as_sexpr(otimes(A,B)) == "(otimes :A :B)"
@test as_sexpr(otimes(f,g)) == "(otimes :f :g)"
@test as_sexpr(compose(otimes(f,f),otimes(g,g))) == "(compose (otimes :f :f) (otimes :g :g))"

@test as_infix(otimes(A,B)) == "A⊗B"
@test as_infix(otimes(f,g)) == "f⊗g : A⊗B → B⊗A"
@test as_infix(mor(:f, I, A)) == "f : I → A"
@test as_infix(compose(otimes(f,f),otimes(g,g))) == "(f⊗f) (g⊗g) : A⊗A → A⊗A"
@test as_infix(otimes(compose(f,g),compose(g,f))) == "(f g)⊗(g f) : A⊗B → A⊗B"
