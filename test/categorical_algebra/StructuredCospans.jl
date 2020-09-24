module TestStructuredCospans
using Test

using Catlab.Theories, Catlab.CategoricalAlgebra,
  Catlab.CategoricalAlgebra.FinSets, Catlab.CategoricalAlgebra.Graphs

# Structured cospans of C-sets
##############################

const OpenGraphOb, OpenGraph = OpenCSetTypes(Graph, :V)
@test OpenGraphOb <: StructuredCospanOb
@test OpenGraph <: StructuredCospan

# Directed fork as open graph with one input and two outputs.
g0 = Graph(4)
add_edges!(g0, [1,2,2], [2,3,4])
g = OpenGraph(g0, Cospan(FinFunction([1], 4), FinFunction([3,4], 4)))
@test apex(g) == g0
@test dom.(legs(g)) == [Graph(1), Graph(2)]
@test feet(g) == [FinSet(1), FinSet(2)]

# Opposite of previous graph.
h0 = Graph(4)
add_edges!(h0, [1,2,3], [3,3,4])
h = OpenGraph(h0, Cospan(FinFunction([1,2], 4), FinFunction([4], 4)))

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
@test compose(g, id(codom(g))) == g
@test compose(id(dom(g)), g) == g

end
