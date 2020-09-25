module TestStructuredCospans
using Test

using Catlab, Catlab.Theories, Catlab.CategoricalAlgebra,
  Catlab.CategoricalAlgebra.FinSets, Catlab.CategoricalAlgebra.Graphs
using Catlab.CategoricalAlgebra.Graphs: TheoryGraph

# Structured cospans of C-sets
##############################

const OpenGraphOb, OpenGraph = OpenCSetTypes(Graph, :V)
@test OpenGraphOb <: StructuredCospanOb
@test OpenGraph <: StructuredCospan

# Directed fork as open graph with one input and two outputs.
g0 = Graph(4)
add_edges!(g0, [1,2,2], [2,3,4])
g = OpenGraph(g0, FinFunction([1],4), FinFunction([3,4],4))
@test apex(g) == g0
@test dom.(legs(g)) == [Graph(1), Graph(2)]
@test feet(g) == [FinSet(1), FinSet(2)]

# Opposite of previous graph.
h0 = Graph(4)
add_edges!(h0, [1,2,3], [3,3,4])
h = OpenGraph(h0, FinFunction([1,2],4), FinFunction([4],4))

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

# Structured cospan of attributed C-sets
########################################

# Non-attributed boundary
#------------------------

@present TheoryWeightedGraph <: TheoryGraph begin
  Weight::Data
  weight::Attr(E,Weight)
end

const WeightedGraph = ACSetType(TheoryWeightedGraph, index=[:src,:tgt])
const OpenWeightedGraphOb, OpenWeightedGraph = OpenACSetTypes(WeightedGraph, :V)

g0 = WeightedGraph{Float64}(2)
add_edge!(g0, 1, 2, weight=1.5)
g = OpenWeightedGraph{Float64}(g0, FinFunction([1],2), FinFunction([2],2))
@test dom.(legs(g)) == [WeightedGraph{Float64}(1), WeightedGraph{Float64}(1)]
@test feet(g) == [FinSet(1), FinSet(1)]

h0 = WeightedGraph{Float64}(3)
add_edges!(h0, [1,1], [2,3], weight=[1.0,2.0])
h = OpenWeightedGraph{Float64}(h0, FinFunction([1],3), FinFunction([2,3],3))
k = compose(g, h)
k0 = apex(k)
@test src(k0) == [1,2,2]
@test tgt(k0) == [2,3,4]
@test subpart(k0, :weight) == [1.5, 1.0, 2.0]

# Attributed boundary
#--------------------

@present TheoryLabeledGraph <: TheoryGraph begin
  Label::Data
  vlabel::Attr(V,Label)
  elabel::Attr(E,Label)
end

const LabeledGraph = ACSetType(TheoryLabeledGraph, index=[:src,:tgt])
const OpenLabeledGraphOb, OpenLabeledGraph = OpenACSetTypes(LabeledGraph, :V)

g0 = LabeledGraph{Symbol}()
add_vertices!(g0, 2, vlabel=[:x,:y])
add_edge!(g0, 1, 2, elabel=:f)
g = OpenLabeledGraph{Symbol}(g0, FinFunction([1],2), FinFunction([2],2))

h0 = LabeledGraph{Symbol}()
add_vertices!(h0, 3, vlabel=[:y,:w,:z])
add_edges!(h0, [1,1], [2,3], elabel=[:g,:h])
h = OpenLabeledGraph{Symbol}(h0, FinFunction([1],3), FinFunction([2,3],3))
lfoot, rfoot = feet(h)
@test lfoot isa ACSet
@test keys(lfoot.tables) == (:V,)
@test nparts(lfoot, :V) == 1
@test nparts(rfoot, :V) == 2
@test subpart(lfoot, :vlabel) == [:y]
@test subpart(rfoot, :vlabel) == [:w,:z]

k = compose(g, h)
k0 = apex(k)
@test src(k0) == [1,2,2]
@test tgt(k0) == [2,3,4]
@test subpart(k0, :vlabel) == [:x, :y, :w, :z]
@test subpart(k0, :elabel) == [:f, :g, :h]

# Incompatible attributes.
set_subpart!(h0, 1, :vlabel, :y′)
h = OpenLabeledGraph{Symbol}(h0, FinFunction([1],3), FinFunction([2,3],3))
@test_throws ErrorException compose(g, h)

end
