module TestSliceCategories

using Test, Catlab

𝒞 = ACSetCategory(Graph())
𝒞′ = Category(𝒞)

############
# Colimits #
############
G = complete_graph(Graph, 2)
Bipartite = SliceC(𝒞′, G)

# Initial 
#########
i = initial[Bipartite]()
@test ob(i).hom ≃ ACSetTransformation(Graph(), G)

# Pushout in Petri, computed as slice in Grph
#############################################
a,b,c = Graph(1), path_graph(Graph, 2), path_graph(Graph, 2)
d = path_graph(Graph, 3)
A = SliceOb(ACSetTransformation(a, G, V=[2])) # □
B = SliceOb(ACSetTransformation(b, G, V=[2,1], E=[2])) # □→⊚
C = SliceOb(ACSetTransformation(b, G, V=[1,2], E=[1])) # ⊚→□
D = SliceOb(ACSetTransformation(d, G, V=[1,2,1], E=[1,2])) # ⊚→□→⊚
f = SliceHom(A,B, ACSetTransformation(a,b,V=[1]); cat=𝒞)
g = SliceHom(A,C, ACSetTransformation(a,c,V=[2]); cat=𝒞)

s = Multispan(A, [f,g], [B, C])
clim = colimit[Bipartite](s)
# the slice map itself is good too but we don't test that yet
@test is_isomorphic(apex(clim).ob, d) 


##########
# Limits #
##########
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
𝒞3 = SliceC(𝒞′, G3) # objects are sets with labels {1,2,3}

A, B = SliceOb.([ACSetTransformation(G2, G3;V=x) for x in [[1,2],[2,1]]])
slic = SliceHom(A,A,id[𝒞](G2); cat=𝒞)
@test is_monic[𝒞3](slic)
@test is_epic[𝒞3](slic)
@test id[𝒞3](A) == slic
slice_lim = π₁, π₂ = product[𝒞3](A,B);

# test universal property
X = SliceOb(ACSetTransformation(G1, G3; V=[1]))
mA, mB = map([A=>[1],B=>[2]]) do (L,x)
  SliceHom(X, L, ACSetTransformation(G1,G2;V=x); cat=𝒞)
end
sp = Span(mA,mB; cat=𝒞3)
u = universal[𝒞3](slice_lim, sp)
@test force(compose[𝒞3](u, π₁); cat=𝒞) == mA
@test force(compose[𝒞3](u, π₂); cat=𝒞) == mB

end # module
