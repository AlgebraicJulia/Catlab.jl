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
AB = GraphSlice.([ACSetTransformation(G2, G3;V=x) for x in [[1,2],[2,1]]])
slice_dia = FreeDiagram(DiscreteDiagram(AB, GraphSliceMorphism))
slice_lim = limit(slice_dia)


span_morphisms = [ACSetTransformation(G1,G2;V=x) for x in [[1],[2]]]
map_to_base = GraphSlice(ACSetTransformation(G1,G3;V=[1]))
toA, toB = [GraphSliceMorphism(map_to_base, ab, span_morphism)
          for (span_morphism, ab) in zip(span_morphisms, AB)]
u = universal(slice_lim, Span(toA, toB))
@test dom(u) == map_to_base
@test codom(u) == apex(slice_lim)
@test force(compose(u, legs(slice_lim)[1]).f) == force(toA.f)

end #module