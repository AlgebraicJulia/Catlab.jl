module TestAbstractWiring

using CompCat.Diagram.AbstractWiring
using Base.Test

A, B = wires(:A), wires(:B)
f = box(:f, A, B)
g = box(:g, B, A)

# Equality of equivalent boxes
@test wires(:A) == wires(:A)
@test box(:f, wires(:A), wires(:B)) == box(:f, wires(:A), wires(:B))

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

# Identity
@test compose(id(A), f) == f
@test compose(f, id(B)) == f

# Monoidal category
###################

# Domains and codomains
@test dom(otimes(f,g)) == otimes(dom(f),dom(g))
@test codom(otimes(f,g)) == otimes(codom(f),codom(g))

# Associativity and unit
I = munit(Wires)
@test otimes(A,I) == A
@test otimes(I,A) == A
@test otimes(otimes(A,B),A) == otimes(A,otimes(B,A))
@test otimes(otimes(f,g),f) == otimes(f,otimes(g,f))

end
