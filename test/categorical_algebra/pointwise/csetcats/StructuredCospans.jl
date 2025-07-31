module TestCSetStructuredCospans

using Test, Catlab

const Grph = ACSetCategory(Graph())
const OpenGraphOb, OpenGraph = OpenCSetTypes(Graph, :V)

# Directed fork as open graph with one input and two outputs.
g0 = Graph(4)
add_edges!(g0, [1,2,2], [2,3,4])

g = OpenGraph(g0, FinFunction([1],4), FinFunction([3,4],4));

@test apex(g) == g0
@test dom.(legs(g)) == [Graph(1), Graph(2)]
@test feet(g) == [FinSet(1), FinSet(2)]
@test dom(g) == OpenGraphOb(FinSet(1))
@test codom(g) == OpenGraphOb(FinSet(2))

# Opposite of previous graph.
h0 = Graph(4)
add_edges!(h0, [1,2,3], [3,3,4])
h = OpenGraph(h0, FinFunction([1,2],4), FinFunction([4],4))

# Structured multicospans.
g′ = OpenGraph(g0, FinFunction([1],4), FinFunction([3],4), FinFunction([4],4))
@test feet(g′) == fill(FinSet(1), 3)

g2 = bundle_legs(g′, [1, (2,3)]);
@test apex(g2) == apex(g)
@test legs(g2) ≃ collect(legs(g))
@test collect(feet(g2)) == collect(feet(g))

# Category
#---------

# Composition.
k = compose(g, h)
@test dom(k) == dom(g)
@test codom(k) == codom(h)
k0 = apex(k)
@test (nv(k0), ne(k0)) == (6, 6)
@test (src(k0), tgt(k0)) == ([1,2,2,3,4,5], [2,3,4,5,5,6])

# Identities.
a = OpenGraphOb(FinSet(3))
@test dom(id(a)) == a
@test codom(id(a)) == a
gg = compose(g, id(codom(g)))
@test apex(gg) == apex(g)
@test force.(legs(gg)) == legs(g)
@test feet(gg) == feet(g)
gg = compose(id(dom(g)), g)
@test apex(gg) == apex(g)
@test force.(legs(gg)) == legs(g)
@test feet(gg) == feet(g)

# Symmetric monoidal category
#----------------------------

a, b = OpenGraphOb(FinSet(3)), OpenGraphOb(FinSet(2))
@test otimes(a, b) == OpenGraphOb(FinSet(5))
@test munit(OpenGraphOb) == OpenGraphOb(FinSet(0))
@test dom(braid(a, b)) == a⊗b
@test codom(braid(b, a)) == b⊗a

bb = force(braid(a,b)⋅braid(b,a))
iab = force(id(a⊗b))
@test apex(bb) == apex(iab)
@test feet(bb) == feet(iab)
# @test force(braid(a,b)⋅braid(b,a)) == force(id(a⊗b)) # 
# Legs are still equal too, module indexing of FinFunctions

k = otimes(g, h)
@test dom(k) == dom(g)⊗dom(h)
@test codom(k) == codom(g)⊗codom(h)
@test (nv(apex(k)), ne(apex(k))) == (8, 6)

# Hypergraph category
#--------------------
@test force(compose(create(a), mcopy(a))) == force(dunit(a))
@test force(compose(mmerge(a), delete(a))) == force(dcounit(a))

@test dom(dagger(g)) == codom(g)
@test codom(dagger(g)) == dom(g)

end # module
