using CompCat.Diagram
using Base.Test

A, B = Wires(:A), Wires(:B)
f = AtomicBox(:f, A, B)
g = AtomicBox(:g, B, A)

# Equality of equivalent boxes
@test Wires(:A) == Wires(:A)
@test AtomicBox(:f, Wires(:A), Wires(:B)) == AtomicBox(:f, Wires(:A), Wires(:B))

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
