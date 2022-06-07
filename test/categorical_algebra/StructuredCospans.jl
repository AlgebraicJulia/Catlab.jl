module TestStructuredCospans
using Test

using Catlab, Catlab.Theories, Catlab.Graphs, Catlab.CategoricalAlgebra
using Catlab.Graphs.BasicGraphs: AbstractGraph, TheoryGraph

# Structured cospans of C-sets
##############################

const OpenGraphOb, OpenGraph = OpenCSetTypes(Graph, :V)

# Directed fork as open graph with one input and two outputs.
g0 = Graph(4)
add_edges!(g0, [1,2,2], [2,3,4])
g = OpenGraph(g0, FinFunction([1],4), FinFunction([3,4],4))
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
@test bundle_legs(g′, [1, (2,3)]) == g

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
@test compose(g, id(codom(g))) == g
@test compose(id(dom(g)), g) == g

# Symmetric monoidal category
#----------------------------

a, b = OpenGraphOb(FinSet(3)), OpenGraphOb(FinSet(2))
@test otimes(a, b) == OpenGraphOb(FinSet(5))
@test munit(OpenGraphOb) == OpenGraphOb(FinSet(0))
@test dom(braid(a, b)) == a⊗b
@test codom(braid(b, a)) == b⊗a
@test force(braid(a,b)⋅braid(b,a)) == force(id(a⊗b))

k = otimes(g, h)
@test dom(k) == dom(g)⊗dom(h)
@test codom(k) == codom(g)⊗codom(h)
@test (nv(apex(k)), ne(apex(k))) == (8, 6)

# Hypergraph category
#--------------------

@test compose(create(a), mcopy(a)) == dunit(a)
@test compose(mmerge(a), delete(a)) == dcounit(a)

@test dom(dagger(g)) == codom(g)
@test codom(dagger(g)) == dom(g)

# Structured cospan of attributed C-sets
########################################

# Non-attributed boundary
#------------------------

const OpenWeightedGraphOb, OpenWeightedGraph = OpenACSetTypes(WeightedGraph, :V)

g0 = WeightedGraph{Float64}(2)
add_edge!(g0, 1, 2, weight=1.5)
g = OpenWeightedGraph{Float64}(g0, FinFunction([1],2), FinFunction([2],2))

h0 = WeightedGraph{Float64}(3)
add_edges!(h0, [1,1], [2,3], weight=[1.0,2.0])
h = OpenWeightedGraph{Float64}(h0, FinFunction([1],3), FinFunction([2,3],3))
@test dom.(legs(h)) == [WeightedGraph{Float64}(1), WeightedGraph{Float64}(2)]
@test feet(h) == [FinSet(1), FinSet(2)]
@test dom(h) == OpenWeightedGraphOb{Float64}(FinSet(1))
@test codom(h) == OpenWeightedGraphOb{Float64}(FinSet(2))

k = compose(g, h)
k0 = apex(k)
@test src(k0) == [1,2,2]
@test tgt(k0) == [2,3,4]
@test subpart(k0, :weight) == [1.5, 1.0, 2.0]

# Attributed boundary
#--------------------

@present TheoryVELabeledGraph <: TheoryGraph begin
  Label::AttrType
  vlabel::Attr(V,Label)
  elabel::Attr(E,Label)
end

@acset_type VELabeledGraph(TheoryVELabeledGraph, index=[:src,:tgt]) <: AbstractGraph
const VELGraph = VELabeledGraph

const OpenVELGraphOb, OpenVELGraph = OpenACSetTypes(VELGraph, :V)

g0 = VELGraph{Symbol}()
add_vertices!(g0, 2, vlabel=[:x,:y])
add_edge!(g0, 1, 2, elabel=:f)
g = OpenVELGraph{Symbol}(g0, FinFunction([1],2), FinFunction([2],2))

h0 = VELGraph{Symbol}()
add_vertices!(h0, 3, vlabel=[:y,:w,:z])
add_edges!(h0, [1,1], [2,3], elabel=[:g,:h])
h = OpenVELGraph{Symbol}(h0, FinFunction([1],3), FinFunction([2,3],3))
lfoot, rfoot = feet(h)
@test nparts(rfoot, :V) == 2
@test subpart(rfoot, :vlabel) == [:w,:z]
@test dom(h) == OpenVELGraphOb{Symbol}(FinSet(1), vlabel=:y)
@test codom(h) == OpenVELGraphOb{Symbol}(FinSet(2), vlabel=[:w,:z])

# Category
#---------

k = compose(g, h)
k0 = apex(k)
@test src(k0) == [1,2,2]
@test tgt(k0) == [2,3,4]
@test subpart(k0, :vlabel) == [:x, :y, :w, :z]
@test subpart(k0, :elabel) == [:f, :g, :h]

# Incompatible attributes.
set_subpart!(h0, 1, :vlabel, :y′)
h = OpenVELGraph{Symbol}(h0, FinFunction([1],3), FinFunction([2,3],3))
@test_throws ErrorException compose(g, h)

# Symmetric monoidal category
#----------------------------

k = otimes(g, h)
@test dom(k) == dom(g)⊗dom(h)
@test codom(k) == codom(g)⊗codom(h)
@test (nv(apex(k)), ne(apex(k))) == (5, 3)

a = OpenVELGraphOb{Symbol}(FinSet(2), vlabel=[:u,:v])
b = OpenVELGraphOb{Symbol}(FinSet(3), vlabel=[:x,:y,:z])
@test dom(braid(a, b)) == a⊗b
@test codom(braid(a, b)) == b⊗a

# Structured cospan of multiply attributed C-sets
#################################################

# Attributed boundary
#--------------------

@present TheoryMultiplyAttributedGraph <: TheoryGraph begin
  Length::AttrType
  Size::AttrType
  Label::AttrType
  vlabel::Attr(V,Label)
  elabel::Attr(E,Label)
  vsize::Attr(V, Size)
  elength::Attr(E, Length)
end

@acset_type MAGraph(TheoryMultiplyAttributedGraph, index=[:src,:tgt]) <: AbstractGraph
const OpenMAGraphOb, OpenMAGraph = OpenACSetTypes(MAGraph, :V)

g0 = @acset MAGraph{Int, Float64, Symbol} begin
  V = 5
  E = 3
  vlabel = [:a, :b, :c, :d, :e]
  elabel = [:a, :b, :c]
  vsize = [0.0, 1.0, 3.0, 3.0, 4.0]
  elength = [1,2,3]
  src = [1, 2, 3]
  tgt = [3, 4, 5]
end
g = OpenMAGraph{Int, Float64, Symbol}(g0, FinFunction([1],5), FinFunction([3,4],5))

g′ = OpenMAGraph{Int, Float64, Symbol}(g0, FinFunction([1],5), FinFunction([3],5), FinFunction([4],5))
@test bundle_legs(g′, [1, (2,3)]) == g

end
