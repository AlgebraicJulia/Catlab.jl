module TestACSetStructuredCospans

using Test, Catlab

# Interface schema: one object, no attributes
#--------------------------------------------

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

# Interface schema: one object, with attributes
#----------------------------------------------

@present SchVELabeledGraph <: SchGraph begin
  Label::AttrType
  vlabel::Attr(V,Label)
  elabel::Attr(E,Label)
end

@acset_type VELabeledGraph(SchVELabeledGraph, index=[:src,:tgt]) <: AbstractGraph
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

# Category.
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

# Symmetric monoidal category.
k = otimes(g, h)
@test dom(k) == dom(g)⊗dom(h)
@test codom(k) == codom(g)⊗codom(h)
@test (nv(apex(k)), ne(apex(k))) == (5, 3)

a = OpenVELGraphOb{Symbol}(FinSet(2), vlabel=[:u,:v])
b = OpenVELGraphOb{Symbol}(FinSet(3), vlabel=[:x,:y,:z])
@test dom(braid(a, b)) == a⊗b
@test codom(braid(a, b)) == b⊗a

@present SchWeightedLabeledGraph <: SchWeightedGraph begin
  Label::AttrType
  vlabel::Attr(V,Label)
  elabel::Attr(E,Label)
end

@acset_type WeightedLabeledGraph(SchWeightedLabeledGraph) <: AbstractGraph
const OpenWLGraphOb, OpenWLGraph = OpenACSetTypes(WeightedLabeledGraph, :V)

g0 = @acset WeightedLabeledGraph{Float64,Symbol} begin
  V = 5
  E = 3
  src = [1, 2, 3]
  tgt = [3, 4, 5]
  vlabel = [:a, :b, :c, :d, :e]
  elabel = [:a, :b, :c]
  weight = [1., 2., 3.]
end
g = OpenWLGraph{Float64,Symbol}(g0, FinFunction([1],5), FinFunction([3,4],5))
g′ = OpenWLGraph{Float64,Symbol}(g0, FinFunction([1],5),
                               FinFunction([3],5), FinFunction([4],5))
@test bundle_legs(g′, [1, (2,3)]) ≃ g

# Interface schema: many objects, with attributes
#------------------------------------------------

# This is actually a semi-globular set because there are no degeneracies.
@present SchWeighted2DGlobularSet <: SchWeightedGraph begin
  Cell::Ob
  (src2, tgt2)::Hom(Cell, E)
  compose(src2, src) == compose(tgt2, src)
  compose(src2, tgt) == compose(tgt2, tgt)

  weight2::Attr(Cell, Weight)
end

@acset_type Weighted2DGlobularSet(SchWeighted2DGlobularSet) <: HasGraph
const OpenWeighted2DGlobularSetOb, OpenWeighted2DGlobularSet =
  OpenACSetTypes(Weighted2DGlobularSet, WeightedGraph)

v = WeightedGraph{Float64}(1)
e1, e2 = WeightedGraph{Float64}(2), WeightedGraph{Float64}(2)
add_edge!(e1, 1, 2, weight=1.)
add_edge!(e2, 1, 2, weight=2.)

cell = @acset Weighted2DGlobularSet{Float64} begin
  V = 2
  E = 2
  Cell = 1
  src = [1,1]; tgt = [2,2]
  src2 = [1]; tgt2 = [2]
  weight = [1., 2.]
  weight2 = [1.]
end

# Composing along vertices.
g = OpenWeighted2DGlobularSet{Float64}(cell, OpenACSetLeg(v, V=[1]),
                                     OpenACSetLeg(v, V=[2]))
h = apex(compose(g, g))
@test (src(h), tgt(h)) == ([1,1,2,2], [2,2,3,3])
@test (h[:src2], h[:tgt2]) == ([1,3], [2,4])
@test (h[:weight], h[:weight2]) == ([1.,2.,1.,2.], [1.,1.])

# Composing along edges.
g = OpenWeighted2DGlobularSet{Float64}(cell, OpenACSetLeg(e1, V=[1,2], E=[1]),
                                     OpenACSetLeg(e2, V=[1,2], E=[2]))
h = apex(compose(g, dagger(g)))
@test (src(h), tgt(h)) == ([1,1,1], [2,2,2])
@test (h[:src2], h[:tgt2]) == ([1,3], [2,2])
@test (h[:weight], h[:weight2]) == ([1.,2.,1], [1.,1.])

end # module
