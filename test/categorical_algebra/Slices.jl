module TestSlices
using Test

using Catlab.Theories, Catlab.CategoricalAlgebra, Catlab.Graphs

"""
A product in a slice category is equivalent to a pullback. Here we work with
discrete graphs:

PB     B=2
        ↓ id
A=2 ⟶ C=3
   swap

The pullback of A and B has two elements:
- one element mapping to (a₂,b₁) - which both map to c₁
- one element mapping to (a₁,b₂) - which both map to c₂

Given slice morphisms into A and B (say, a single element set which maps to c₁,
which forces its map to A to point to a₂ and its map to B to point to b₁), the
universal property gives a map into the limit object, so it picks the element
that maps to (a₂,b₁).
"""

G2,G1,G3 = Graph.([2,1,3])
GraphSlice = Slice{Graph, ACSetTransformation}
GraphSliceMorphism = SliceMorphism{Graph, ACSetTransformation}
A, B = GraphSlice.([ACSetTransformation(G2, G3;V=x) for x in [[1,2],[2,1]]])
slice_dia = FreeDiagram(DiscreteDiagram([A,B], GraphSliceMorphism))
slice_lim = limit(slice_dia)


mA, mB = [ACSetTransformation(G1,G2;V=x) for x in [[1],[2]]]
map_to_base = GraphSlice(ACSetTransformation(G1,G3;V=[1]))
toA = GraphSliceMorphism(map_to_base, A, mA)
toB = GraphSliceMorphism(map_to_base, B, mB)
u = universal(slice_lim, Span(toA, toB))
@test dom(u) == map_to_base
@test codom(u) == apex(slice_lim)
@test force(compose(u, legs(slice_lim)[1]).f) == force(toA.f)


# Pushout complement in Petri, computed as slice in Grph
two = @acset Graph begin V=2; E=2; src=[1,2]; tgt=[2,1] end
a,b,c = Graph(1), path_graph(Graph, 2), path_graph(Graph, 3)
A = GraphSlice(ACSetTransformation(a, two, V=[2])) # a transition
B = GraphSlice(ACSetTransformation(b, two, V=[2,1], E=[2]))
C = GraphSlice(ACSetTransformation(c, two, V=[1,2,1], E=[1,2]))
ff = ACSetTransformation(a,b,V=[1])
gg = ACSetTransformation(b,c,V=[2,3], E=[2])
f = GraphSliceMorphism(A,B,ff)
g = GraphSliceMorphism(B,C,gg)
pc1, pc2 = pushout_complement(ComposablePair(ff,gg))
p1, p2 = pushout_complement(f,g)

# Colimit: a pushout of slices
#------------------------------
# do the pushout associated with the pushout complement above
slice_dia = FreeDiagram{GraphSlice,GraphSliceMorphism}(Multispan(A, [f, p1]))
clim = colimit(slice_dia)
@test is_isomorphic(dom(apex(clim)), c)
#pushout(f, p1)
colimit(Span(f, p1))

# DPO of slices: do the pushout complement and add an extra state
R = GraphSlice(ACSetTransformation(Graph(2), two, V=[2, 1]))
r = GraphSliceMorphism(A,R,ACSetTransformation(a, Graph(2), V=[1]))
res = rewrite_match(f, r, g)
@test is_isomorphic(dom(res), apex(coproduct(b, Graph(1))))
end #module