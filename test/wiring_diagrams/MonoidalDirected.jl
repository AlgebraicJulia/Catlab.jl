module TestMonoidalDirectedWiringDiagrams
using Test

using Catlab.Theories, Catlab.WiringDiagrams

# Categorical interface
#######################

# Category
#---------

# Generators
A, B = Ports([:A]), Ports([:B])
f = singleton_diagram(Box(:f,A,B))
g = singleton_diagram(Box(:g,B,A))
@test nboxes(f) == 1
@test boxes(f) == [ Box(:f,A,B) ]
@test nwires(f) == 2

# Composition
@test nboxes(compose(f,g)) == 2
@test boxes(compose(f,g)) == [ Box(:f,A,B), Box(:g,B,A) ]
@test nwires(compose(f,g)) == 3

# Domains and codomains
@test dom(f) == Ports([:A])
@test codom(f) == Ports([:B])
@test dom(compose(f,g)) == Ports([:A])
@test codom(compose(f,g)) == Ports([:A])

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

# Permutations on DWDs with GAT exprs.
A, B, C, D = Ob(FreeSymmetricMonoidalCategory, :A, :B, :C, :D)
X_expr, Y_expr = otimes(A, B), otimes(C, D)
W_expr = otimes(X_expr, Y_expr)
X, Y, W = to_wiring_diagram.([X_expr, Y_expr, W_expr])
@test permute(W, [1,2,3,4]) == id(W)
@test permute(W, [3,4,1,2]) == braid(X,Y)

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
A = Ports([:A])
@test compose(mcopy(A), otimes(id(A),mcopy(A))) == mcopy(A,3)
@test compose(mcopy(A), otimes(mcopy(A),id(A))) == mcopy(A,3)

# Commutativity
@test compose(mcopy(A), braid(A,A)) == mcopy(A)

# Unitality
@test compose(mcopy(A), otimes(id(A),delete(A))) == id(A)

# Cartesian categories
A = Ports{ThCartesianCategory}([:A])
@test mcopy(A) == mcopy(Ports([:A]))
@test delete(A) == delete(Ports([:A]))
@test_throws MethodError mmerge(A)
@test_throws MethodError create(A)

# Codiagonals
#------------

# Domains and codomains
@test dom(mmerge(Ports([:A]))) == Ports([:A,:A])
@test codom(mmerge(Ports([:A]))) == Ports([:A])
@test dom(mmerge(Ports([:A,:B]),3)) == Ports([:A,:B,:A,:B,:A,:B])
@test codom(mmerge(Ports([:A,:B]),3)) == Ports([:A,:B])

# Associativity
A = Ports([:A])
@test compose(otimes(id(A),mmerge(A)), mmerge(A)) == mmerge(A,3)
@test compose(otimes(mmerge(A),id(A)), mmerge(A)) == mmerge(A,3)

# Commutativity
@test compose(braid(A,A), mmerge(A)) == mmerge(A)

# Unitality
@test compose(otimes(id(A),create(A)), mmerge(A)) == id(A)

# Cocartesian categories
A = Ports{ThCocartesianCategory}([:A])
@test mmerge(A) == mmerge(Ports([:A]))
@test create(A) == create(Ports([:A]))
@test_throws MethodError mcopy(A)
@test_throws MethodError delete(A)

# Bidiagonals
#------------

# Monoidal categories with bidiagonals, and non-naturality of explicit
# representation.
A = Ports{ThMonoidalCategoryWithBidiagonals}([:A])
@test boxes(mcopy(A)) == [ Junction(:A,1,2) ]
@test boxes(mcopy(otimes(A,A))) == repeat([ Junction(:A,1,2) ], 2)
@test compose(create(A), mcopy(A)) != create(otimes(A,A))
@test compose(mmerge(A), delete(A)) != delete(otimes(A,A))

# Biproduct categories, and naturality of implicit representation.
A = Ports{ThBiproductCategory}([:A])
@test compose(create(A), mcopy(A)) == create(otimes(A,A))
@test compose(mmerge(A), delete(A)) == delete(otimes(A,A))

# Dagger category
#----------------

f = singleton_diagram(ThDaggerSymmetricMonoidalCategory, Box(:f,[:A],[:B]))
g = singleton_diagram(ThDaggerSymmetricMonoidalCategory, Box(:g,[:B],[:A]))

@test boxes(dagger(f)) == [ BoxOp{:dagger}(Box(:f,[:A],[:B])) ]

# Domain and codomain
@test dom(dagger(f)) == codom(f)
@test codom(dagger(f)) == dom(f)

# Functoriality
@test is_isomorphic(dagger(compose(f,g)), compose(dagger(g),dagger(f)))
@test dagger(otimes(f,g)) == otimes(dagger(f),dagger(g))

# Involutivity
@test dagger(dagger(f)) == f
@test dagger(dagger(compose(f,g))) == compose(f,g)
@test dagger(dagger(otimes(f,g))) == otimes(f,g)

# Compact closed category
#------------------------

### Duals

A, B = [ Ports{ThCompactClosedCategory}([sym]) for sym in [:A, :B] ]
I = munit(typeof(A))

@test boxes(dunit(A)) == [ Junction(:A, [], [PortOp{:dual}(:A), :A]) ]
@test boxes(dcounit(A)) == [ Junction(:A, [:A, PortOp{:dual}(:A)], []) ]

# Domains and codomains
@test dom(dunit(A)) == I
@test codom(dunit(A)) == otimes(dual(A),A)
@test dom(dcounit(A)) == otimes(A,dual(A))
@test codom(dcounit(A)) == I

# Coherence relations
@test is_isomorphic(dunit(otimes(A,B)),
                    compose(dunit(B), otimes(id(dual(B)), dunit(A), id(B))))
@test is_isomorphic(dcounit(otimes(A,B)),
                    compose(otimes(id(A), dcounit(B), id(dual(A))), dcounit(A)))

### Adjoint mates

f = singleton_diagram(ThCompactClosedCategory, Box(:f,[:A],[:B]))
g = singleton_diagram(ThCompactClosedCategory, Box(:g,[:B],[:A]))

@test boxes(mate(f)) == [ BoxOp{:mate}(Box(:f,[:A],[:B])) ]

# Domain and codomain
@test dom(mate(f)) == dual(codom(f))
@test codom(mate(f)) == dual(dom(f))

# Functoriality
@test is_isomorphic(mate(compose(f,g)), compose(mate(g),mate(f)))
@test is_isomorphic(mate(otimes(f,g)), otimes(mate(g),mate(f)))

# Involutivity
@test mate(mate(f)) == f
@test mate(mate(compose(f,g))) == compose(f,g)
@test mate(mate(otimes(f,g))) == otimes(f,g)

# Traced monoidal category
#-------------------------

const TracedMon = ThTracedMonoidalCategory
A, B, X, Y = [ Ports{TracedMon}([sym]) for sym in [:A,:B,:X,:Y] ]
I = munit(typeof(A))
f = singleton_diagram(TracedMon, Box(:f, [:X,:A], [:X,:B]))

# Domain and codomain
@test dom(trace(X, A, B, f)) == A
@test codom(trace(X, A, B, f)) == B

# Naturality
g = singleton_diagram(TracedMon, Box(:g, [:A], [:A]))
h = singleton_diagram(TracedMon, Box(:h, [:B], [:B]))
@test trace(X, compose(id(X)⊗g, f, id(X)⊗h)) == compose(g, trace(X,f), h)

# Stength, aka superposing
g = singleton_diagram(TracedMon, Box(:g, [:C], [:C]))
@test trace(X, otimes(f,g)) == otimes(trace(X,f), g)

# Symmetry sliding
f = singleton_diagram(TracedMon, Box(:f, [:X,:Y,:A], [:Y,:X,:B]))
@test trace(X⊗Y, compose(f, braid(Y,X)⊗id(B))) ==
  trace(Y⊗X, compose(braid(Y,X)⊗id(A), f))

# Vanishing
f = singleton_diagram(TracedMon, Box(:f, [:X,:Y,:A], [:X,:Y,:B]))
@test trace(X⊗Y, f) == trace(Y, trace(X, f))
f = singleton_diagram(TracedMon, Box(:f, [:A], [:B]))
@test trace(I, f) == f

# Yanking
@test trace(X, braid(X,X)) == id(X)

# Bicategory of relations
#------------------------

A, B = [ Ports{ThBicategoryRelations}([sym]) for sym in [:A, :B] ]
R = singleton_diagram(ThBicategoryRelations, Box(:R,[:A],[:B]))
S = singleton_diagram(ThBicategoryRelations, Box(:S,[:A],[:B]))

# Domains and codomains
@test dom(meet(R,S)) == A
@test codom(meet(R,S)) == B
@test dom(top(A,B)) == A
@test codom(top(A,B)) == B

# Units and counits
@test dunit(A) == merge_junctions(compose(create(A), mcopy(A)))
@test dcounit(A) == merge_junctions(compose(mmerge(A), delete(A)))

# Abelian bicategory of relations
#--------------------------------

A, B = [ Ports{ThAbelianBicategoryRelations}([sym]) for sym in [:A, :B] ]
R = singleton_diagram(ThAbelianBicategoryRelations, Box(:R,[:A],[:B]))
S = singleton_diagram(ThAbelianBicategoryRelations, Box(:S,[:A],[:B]))

# Domains and codomains.
@test dom(plus(A)) == dom(mmerge(A)) && codom(plus(A)) == codom(mmerge(A))
@test dom(coplus(A)) == dom(mcopy(A)) && codom(coplus(A)) == codom(mcopy(A))
@test dom(zero(A)) == dom(create(A)) && codom(zero(A)) == codom(create(A))
@test dom(cozero(A)) == dom(delete(A)) && codom(cozero(A)) == codom(delete(A))

@test dom(join(R,S)) == A
@test codom(join(R,S)) == B
@test dom(bottom(A,B)) == A
@test codom(bottom(A,B)) == B

# Distinctness of "multiplicative" and "additive" (co)diagonals.
@test plus(A) != mmerge(A)
@test coplus(A) != mcopy(A)
@test zero(A) != create(A)
@test cozero(A) != delete(A)

# Junctions
###########

# Add and remove junctions
#-------------------------

A, B, C = [ Ports([sym]) for sym in [:A, :B, :C] ]
f = singleton_diagram(Box(:f, [:A], [:B]))
g = singleton_diagram(Box(:g, [:B], [:C]))

# Copies.
d = compose(f, mcopy(B))
junctioned = compose(f, junction_diagram(B,1,2))
@test add_junctions(d) == junctioned
@test rem_junctions(junctioned) == d

d = compose(mcopy(A), otimes(f,f))
junctioned = compose(junction_diagram(A,1,2), otimes(f,f))
@test is_isomorphic(add_junctions(d), junctioned)
@test rem_junctions(junctioned) == d

# Merges.
d = compose(mmerge(A), f)
junctioned = compose(junction_diagram(A,2,1), f)
@test is_isomorphic(add_junctions(d), junctioned)
@test rem_junctions(junctioned) == d

d = compose(otimes(f,f), mmerge(B))
junctioned = compose(otimes(f,f), junction_diagram(B,2,1))
@test add_junctions(d) == junctioned
@test rem_junctions(junctioned) == d

# Deletions.
d = compose(f, delete(B))
junctioned = compose(f, junction_diagram(B,1,0))
@test add_junctions(d) == junctioned
@test rem_junctions(junctioned) == d

# Creations.
d = compose(create(A), f)
junctioned = compose(junction_diagram(A,0,1), f)
@test is_isomorphic(add_junctions(d), junctioned)
@test rem_junctions(junctioned) == d

# Copies, merges, deletions, and creations, all at once.
d = compose(create(A), f, mcopy(B), mmerge(B), g, delete(C))
junctioned = compose(junction_diagram(A,0,1), f, junction_diagram(B,1,2),
                     junction_diagram(B,2,1), g, junction_diagram(C,1,0))
actual = add_junctions(d)
@test is_isomorphic(actual, junctioned)
@test rem_junctions(junctioned) == d

# Simplify junctions
#-------------------

A = Ports([:A])
j = junction_diagram

# Comonoid laws.
@test merge_junctions(j(A,1,2)⋅(j(A,1,2)⊗id(A))) ==
  j(A,1,3)⋅permute(A⊗A⊗A,[3,1,2]) # FIXME: Shouldn't need permutation.
@test merge_junctions(j(A,1,2)⋅(id(A)⊗j(A,1,2))) == j(A,1,3)
@test merge_junctions(j(A,1,2)⋅(j(A,1,0)⊗id(A))) == j(A,1,1)
@test merge_junctions(j(A,1,2)⋅(id(A)⊗j(A,1,0))) == j(A,1,1)

# Caps and cups.
@test merge_junctions(j(A,0,1)⋅j(A,1,2)) == j(A,0,2)
@test merge_junctions(j(A,2,1)⋅j(A,1,0)) == j(A,2,0)

# Zigzag laws.
@test merge_junctions((id(A)⊗j(A,0,2))⋅(j(A,2,0)⊗id(A))) == j(A,1,1)
@test merge_junctions((j(A,0,2)⊗id(A))⋅(id(A)⊗j(A,2,0))) == j(A,1,1)

end
