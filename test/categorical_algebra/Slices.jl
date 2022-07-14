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
# create limit
G2,G1,G3 = Graph.([2,1,3])
A, B = Slice.([ACSetTransformation(G2, G3;V=x) for x in [[1,2],[2,1]]])
@test force(id(A)) == force(SliceHom(A,A,id(G2)))
slice_dia = FreeDiagram(DiscreteDiagram([A,B], SliceHom))
slice_lim = limit(slice_dia)

# test universal property
mA, mB = [ACSetTransformation(G1,G2;V=x) for x in [[1],[2]]]
map_to_base = Slice(ACSetTransformation(G1,G3;V=[1]))
toA = SliceHom(map_to_base, A, mA)
toB = SliceHom(map_to_base, B, mB)
u = universal(slice_lim, Span(toA, toB))
@test dom(u) == map_to_base
@test codom(u) == apex(slice_lim)
@test force(compose(u, legs(slice_lim)[1]).f) == force(toA.f)


# Colimit: a pushout of slices
#------------------------------

# Pushout in Petri, computed as slice in Grph
two = @acset Graph begin V=2; E=2; src=[1,2]; tgt=[2,1] end
a,b,c = Graph(1), path_graph(Graph, 2), path_graph(Graph, 2)
d = path_graph(Graph, 3)
A = Slice(ACSetTransformation(a, two, V=[2])) # □
B = Slice(ACSetTransformation(b, two, V=[2,1], E=[2])) # □→⊚
C = Slice(ACSetTransformation(b, two, V=[1,2], E=[1])) # ⊚→□
D = Slice(ACSetTransformation(d, two, V=[1,2,1], E=[1,2])) # ⊚→□→⊚
ff = ACSetTransformation(a,b,V=[1])
gg = ACSetTransformation(a,c,V=[2])
f = SliceHom(A,B,ff)
g = SliceHom(A,C,gg)

slice_dia = FreeDiagram{Slice,SliceHom}(Multispan(A, [f, g]))
clim = colimit(slice_dia)
@test is_isomorphic(dom(apex(clim)), d)

end # module
