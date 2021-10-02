module TestStructuredCospans
using Test

using Catlab, Catlab.Theories, Catlab.Graphs,
  Catlab.CategoricalAlgebra, Catlab.CategoricalAlgebra.FinSets
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

@present TheoryLabeledGraph <: TheoryGraph begin
  Label::AttrType
  vlabel::Attr(V,Label)
  elabel::Attr(E,Label)
end

@acset_type LabeledGraph(TheoryLabeledGraph, index=[:src,:tgt]) <: AbstractGraph
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
@test nparts(rfoot, :V) == 2
@test subpart(rfoot, :vlabel) == [:w,:z]
@test dom(h) == OpenLabeledGraphOb{Symbol}(FinSet(1), vlabel=:y)
@test codom(h) == OpenLabeledGraphOb{Symbol}(FinSet(2), vlabel=[:w,:z])

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
h = OpenLabeledGraph{Symbol}(h0, FinFunction([1],3), FinFunction([2,3],3))
@test_throws ErrorException compose(g, h)

# Symmetric monoidal category
#----------------------------

k = otimes(g, h)
@test dom(k) == dom(g)⊗dom(h)
@test codom(k) == codom(g)⊗codom(h)
@test (nv(apex(k)), ne(apex(k))) == (5, 3)

a = OpenLabeledGraphOb{Symbol}(FinSet(2), vlabel=[:u,:v])
b = OpenLabeledGraphOb{Symbol}(FinSet(3), vlabel=[:x,:y,:z])
@test dom(braid(a, b)) == a⊗b
@test codom(braid(a, b)) == b⊗a


# EXAMPLE GRAPHS
#---------------
G1 = Graph(1);
G2 = Graph(2);
G3 = Graph(3);

Loop = Graph(1);
add_edge!(Loop, 1, 1);

Arrow = Graph(2);
add_edge!(Arrow, 1, 2);

BiArrow = Graph(2)
add_edges!(BiArrow, [1,2],[2,1])

Three = Graph(3);
add_edges!(Three, [1,2], [2,3]);

Square = Graph(4)
add_edges!(Square,[1,1,2,3],[2,3,4,4]);

Tri = Graph(3)
add_edges!(Tri,[1,1,2],[2,3,3]);

LoopTri = Graph(3)
add_edges!(LoopTri,[1,1,1,2],[1,2,3,3]);

"""
  3→4
 ╱  ↓
1→2→5
"""
Trap = Graph(5);
add_edges!(Trap,[1,2,1,3,4],[2,5,3,4,5]);

CSpan = Graph(3);
add_edges!(CSpan, [1,3],[2,2]);

Cycle = Graph(2);
add_edges!(Cycle, [1,2],[2,1]);

# Example Spans
#--------------

id_1 = id(Graph(1));
id_2 = id(Graph(2));
flip = CSetTransformation(G2, G2, V=[2,1]);
f12 = CSetTransformation(G1, G2, V=[1]);
f22 = CSetTransformation(G1, G2, V=[2]);

sp1 = Span(id_1, id_1);
sp2 = Span(id_2, id_2);
flipflip = Span(flip, flip);

# Open Graphs
#------------
o1 = OpenGraph(G1, id_1[:V], id_1[:V]);
o2 = OpenGraph(G2, f12[:V], f22[:V]);
openloop = OpenGraph(Loop, id_1[:V], id_1[:V]);
openp2 = OpenGraph(path_graph(Graph, 3),
                   FinFunction([1], 3), FinFunction([3], 3))

openarr = OpenGraph(Arrow, f12[:V], f22[:V]);
openarr21 = OpenGraph(Arrow, id_2[:V], f22[:V]);
open3 = OpenGraph(Three,
                  FinFunction([2,1], 3),
                  FinFunction([3,2], 3));
opensquare = OpenGraph(Square,
                       FinFunction([1], 4),
                       FinFunction([2], 4));
opensquare2 = OpenGraph(Square,
                        FinFunction([1], 4),
                        FinFunction([4], 4));
opentrap = OpenGraph(Trap,
                     FinFunction([1,2], 5),
                     FinFunction([2,5], 5));
opencspan = OpenGraph(CSpan,
                        FinFunction([2,1], 3),
                        FinFunction([2], 3));
opencycle = OpenGraph(Cycle,  flip[:V], f22[:V]);

# Graph Transformations
#----------------------
gm1 = ACSetTransformation(G1, Loop, V=[1]);
up_ = ACSetTransformation(G2, Arrow, V=[1,2]);
down_ = ACSetTransformation(G2, G1, V=[1,1]);
tosquare = ACSetTransformation(Three, Square, V=[1,2,4],E=[1,3]);
totrap = ACSetTransformation(Three, Trap, V=[1,2,5], E=[1,2]);
tocspan = ACSetTransformation(Arrow, CSpan, V=[1,2], E=[1]);
tocycle = ACSetTransformation(Arrow, Cycle, V=[1,2], E=[1]);

rem_loop_l = StructuredMultiCospanHom(o1,
  openloop, ACSetTransformation[gm1, id_1, id_1])
triv = StructuredMultiCospanHom(o1, o1,
  ACSetTransformation[id_1, id_1, id_1])
squash_l = StructuredMultiCospanHom(o2, openarr,
  ACSetTransformation[up_, id_1, id_1])
squash_r = StructuredMultiCospanHom(o2, o1,
  ACSetTransformation[down_, id_1, id_1])
rem_loop = openrule(Span(rem_loop_l, triv))
add_loop = openrule(Span(triv, rem_loop_l))
squash = openrule(Span(squash_l, squash_r))
square_m = StructuredMultiCospanHom(openarr, opensquare,
  ACSetTransformation[ACSetTransformation(Arrow, Square, V=[1,2], E=[1]), id_1, id_1])

res = open_rewrite_match(squash, square_m)
@test is_isomorphic(apex(res), Tri)

res = open_rewrite_match(composeV_(squash, add_loop), square_m)
@test is_isomorphic(apex(res), LoopTri)

sqsq = composeH_(squash, squash); # squashes a path of length 2 into a point
sqsq_m = StructuredMultiCospanHom(openp2, opensquare2,
  ACSetTransformation[ACSetTransformation(
    path_graph(Graph, 3), Square, V=[1,2,4], E=[1,3]), id_1, id_1])
res = open_rewrite_match(sqsq, sqsq_m)
# squash one path of a commutative square and obtain •⇆•
@test is_isomorphic(apex(res), BiArrow)

end #module