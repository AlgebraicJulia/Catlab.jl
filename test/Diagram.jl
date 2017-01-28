using CompCat.Diagram
using Base.Test

A, B = Wires(:A), Wires(:B)
f = AtomicBox(:f, A, B)
g = AtomicBox(:g, B, A)

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
