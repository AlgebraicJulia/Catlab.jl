module TestMonoidalUndirectedWiringDiagrams
using Test

using Catlab.Theories, Catlab.WiringDiagrams
using Catlab.CategoricalAlgebra.CSets: subpart

# Categorical interface
#######################

const HDOb = HypergraphDiagramOb{Symbol,Symbol}
const HDHom = HypergraphDiagramHom{Symbol,Symbol}

# Category
#---------

# Domains and codomains
A, B = HDOb([:A]), HDOb([:B])
f = HDHom(singleton_diagram(A⊗B, name=:f), dom=BitArray([1,0]))
g = HDHom(singleton_diagram(B⊗A, name=:g), codom=BitArray([0,1]))
@test subpart(f.diagram, :name) == [:f]
@test subpart(g.diagram, :name) == [:g]
@test dom(f) == A
@test codom(f) == B
@test dom(g) == B
@test codom(g) == A

# Composition and identities
fg = compose(f,g)
@test dom(fg) == A
@test codom(fg) == A
@test nboxes(fg.diagram) == 2
@test njunctions(fg.diagram) == 3
@test compose(id(dom(f)), f) == f
@test compose(f, id(codom(f))) == f

# Symmetric monoidal category
#----------------------------

# Monoidal products
X, Y = HDOb([:A,:B]), HDOb([:C,:D])
I = munit(HDOb)
@test otimes(A,B) == X
@test otimes(X,I) == X
@test otimes(I,X) == X
@test dom(f⊗g) == A⊗B
@test codom(f⊗g) == B⊗A

# Braiding
@test compose(braid(X,Y),braid(Y,X)) == id(otimes(X,Y))

# Hypergraph category
#--------------------

@test compose(create(X), mcopy(X)) == dunit(X)
@test compose(mmerge(X), delete(X)) == dcounit(X)
# XXX: Not equal due to ordering of outer ports, but isomorphic.
#@test (id(B)⊗dunit(A)) ⋅ (id(B)⊗f⊗id(A)) ⋅ (dcounit(B)⊗id(A)) == dagger(f)

end
