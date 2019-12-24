module TestAlgebraicWiringDiagrams
using Test

using Catlab.Doctrines, Catlab.WiringDiagrams

# Categorical interface
#######################

A, B, C, D = Ob(FreeSymmetricMonoidalCategory, :A, :B, :C, :D)
f = Hom(:f, A, B)
g = Hom(:g, B, C)
h = Hom(:h, C, D)

# Category
#---------

# Generators
f = singleton_diagram(Box(Hom(:f,A,B)))
g = singleton_diagram(Box(Hom(:g,B,A)))
@test nboxes(f) == 1
@test boxes(f) == [ Box(Hom(:f,A,B)) ]
@test nwires(f) == 2

# Composition
@test nboxes(compose(f,g)) == 2
@test boxes(compose(f,g)) == [ Box(Hom(:f,A,B)), Box(Hom(:g,B,A)) ]
@test nwires(compose(f,g)) == 3

# Domains and codomains
@test dom(f) == Ports([:A])
@test codom(f) == Ports([:B])
@test dom(compose(f,g)) == Ports([:A])
@test codom(compose(f,g)) == Ports([:A])
@test_throws Exception compose(f,f)

# Associativity
@test compose(compose(f,g),f) == compose(f,compose(g,f))

# Identity
@test compose(id(dom(f)), f) == f
@test compose(f, id(codom(f))) == f

# Symmetric monoidal category
#----------------------------

# Domains and codomains
@test dom(otimes(f,g)) == otimes(dom(f),dom(g))
@test codom(otimes(f,g)) == otimes(codom(f),codom(g))

# Associativity and unit
X, Y = Ports([:A,:B]), Ports([:C,:D])
I = munit(Ports)
@test otimes(X,I) == X
@test otimes(I,X) == X
@test otimes(otimes(X,Y),X) == otimes(X,otimes(Y,X))
@test otimes(otimes(f,g),f) == otimes(f,otimes(g,f))

# Braiding
@test compose(braid(X,Y),braid(Y,X)) == id(otimes(X,Y))

# Permutations
W = otimes(X,Y)
@test permute(W, [1,2,3,4]) == id(W)
@test permute(W, [1,2,3,4], inverse=true) == id(W)
@test permute(W, [3,4,1,2]) == braid(X,Y)
@test permute(W, [3,4,1,2], inverse=true) == braid(Y,X)
@test_throws AssertionError permute(W, [1,2])

# Diagonals
#----------

# Basic composition
d = WiringDiagram(dom(f), otimes(codom(f),codom(f)))
fv1 = add_box!(d, first(boxes(f)))
fv2 = add_box!(d, first(boxes(f)))
add_wires!(d, [
  (input_id(d),1) => (fv1,1),
  (input_id(d),1) => (fv2,1),
  (fv1,1) => (output_id(d),1),
  (fv2,1) => (output_id(d),2),
])
@test compose(mcopy(dom(f)), otimes(f,f)) == d

# Domains and codomains
@test dom(mcopy(Ports([:A]))) == Ports([:A])
@test codom(mcopy(Ports([:A]))) == Ports([:A,:A])
@test dom(mcopy(Ports([:A,:B]),3)) == Ports([:A,:B])
@test codom(mcopy(Ports([:A,:B]),3)) == Ports([:A,:B,:A,:B,:A,:B])

# Associativity
X = Ports([:A])
@test compose(mcopy(X), otimes(id(X),mcopy(X))) == mcopy(X,3)
@test compose(mcopy(X), otimes(mcopy(X),id(X))) == mcopy(X,3)

# Commutativity
@test compose(mcopy(X), braid(X,X)) == mcopy(X)

# Unit
@test compose(mcopy(X), otimes(id(X),delete(X))) == id(X)

# Codiagonals
#------------

# Domains and codomains
@test dom(mmerge(Ports([:A]))) == Ports([:A,:A])
@test codom(mmerge(Ports([:A]))) == Ports([:A])
@test dom(mmerge(Ports([:A,:B]),3)) == Ports([:A,:B,:A,:B,:A,:B])
@test codom(mmerge(Ports([:A,:B]),3)) == Ports([:A,:B])

# Associativity
X = Ports([:A])
@test compose(otimes(id(X),mmerge(X)), mmerge(X)) == mmerge(X,3)
@test compose(otimes(mmerge(X),id(X)), mmerge(X)) == mmerge(X,3)

# Commutativity
@test compose(braid(X,X), mmerge(X)) == mmerge(X)

# Unit
@test compose(otimes(id(X),create(X)), mmerge(X)) == id(X)

# Operadic interface
####################

f, g, h = map([:f, :g, :h]) do sym
  (i::Int) -> singleton_diagram(Box(Hom(Symbol("$sym$i"), A, A)))
end

# Identity
d = compose(f(1),f(2))
@test ocompose(g(1), 1, d) == d
@test ocompose(g(1), [d]) == d
@test ocompose(d, [f(1),f(2)]) == d
@test ocompose(d, 1, f(1)) == d
@test ocompose(d, 2, f(2)) == d

# Associativity
@test ocompose(compose(f(1),f(2)), [
  ocompose(compose(g(1),g(2)), [compose(h(1),h(2)), compose(h(3),h(4))]),
  ocompose(compose(g(3),g(4)), [compose(h(5),h(6)), compose(h(7),h(8))])
]) == ocompose(
  ocompose(compose(f(1),f(2)), [compose(g(1),g(2)), compose(g(3),g(4))]),
  [compose(h(1),h(2)), compose(h(3),h(4)), compose(h(5),h(6)), compose(h(7),h(8))]
)
@test ocompose(
  ocompose(compose(f(1),f(2)), 1, compose(g(1),g(2))),
  3, compose(g(3),g(4))
) == ocompose(
  ocompose(compose(f(1),f(2)), 2, compose(g(3),g(4))),
  1, compose(g(1),g(2))
)

# Junctions
###########

A, B, C, D = Ob(FreeBiproductCategory, :A, :B, :C, :D)
f = Hom(:f, A, B)
g = Hom(:g, B, C)

junction_diagram(args...) = singleton_diagram(Junction(args...))

# Add junctions for copies.
d = to_wiring_diagram(compose(f, mcopy(B)))
junctioned = compose(to_wiring_diagram(f), junction_diagram(:B,1,2))
@test add_junctions(d) == junctioned
@test rem_junctions(junctioned) == d

d = to_wiring_diagram(compose(mcopy(A), otimes(f,f)))
junctioned = compose(junction_diagram(:A,1,2), to_wiring_diagram(otimes(f,f)))
@test is_permuted_equal(add_junctions(d), junctioned, [3,1,2])
@test rem_junctions(junctioned) == d

# Add junctions for merges.
d = to_wiring_diagram(compose(mmerge(A), f))
junctioned = compose(junction_diagram(:A,2,1), to_wiring_diagram(f))
@test is_permuted_equal(add_junctions(d), junctioned, [2,1])
@test rem_junctions(junctioned) == d

d = to_wiring_diagram(compose(otimes(f,f), mmerge(B)))
junctioned = compose(to_wiring_diagram(otimes(f,f)), junction_diagram(:B,2,1))
@test add_junctions(d) == junctioned
@test rem_junctions(junctioned) == d

# Add junctions for deletions.
d = to_wiring_diagram(compose(f, delete(B)))
junctioned = compose(to_wiring_diagram(f), junction_diagram(:B,1,0))
@test add_junctions(d) == junctioned
@test rem_junctions(junctioned) == d

# Add junctions for creations.
d = to_wiring_diagram(compose(create(A), f))
junctioned = compose(junction_diagram(:A,0,1), to_wiring_diagram(f))
@test is_permuted_equal(add_junctions(d), junctioned, [2,1])
@test rem_junctions(junctioned) == d

# Add junctions for copies, merges, deletions, and creations, all at once.
d = to_wiring_diagram(compose(create(A),f,mcopy(B),mmerge(B),g,delete(C)))
junctioned = compose(
  junction_diagram(:A,0,1),
  to_wiring_diagram(f),
  junction_diagram(:B,1,2),
  junction_diagram(:B,2,1),
  to_wiring_diagram(g),
  junction_diagram(:C,1,0)
)
actual = add_junctions(d)
# XXX: An isomorphism test would be more convenient.
perm = [ findfirst([b] .== boxes(actual)) for b in boxes(junctioned) ]
@test is_permuted_equal(actual, junctioned, perm)
@test rem_junctions(junctioned) == d

end
