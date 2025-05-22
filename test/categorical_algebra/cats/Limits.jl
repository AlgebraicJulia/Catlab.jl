""" Tests of limits and colimits in general.

More extensive tests are provided by tests of (co)limits in specific categories
such as Set and FinSet.
"""
module TestLimits

using Test, Catlab

A, B, C = Ob(FreeCategory, :A, :B, :C)
const M = Category(TypeCat(FreeCategory.Meta.M))

# Limits
########
DD(x) = DiscreteDiagram(x)
# Limit data structure.
f, g = Hom(:f, C, A), Hom(:g, C, B)
dia = DD([A,B])
lim = LimitCone(Span(f,g), FreeDiagram(dia))
@test ob(lim) == C
@test apex(lim) == C
@test legs(lim) == [f,g]

lim2 = LimitCone(Span(Hom(:f, C, A),Hom(:g, C, B)), FreeDiagram(DD([A,B])),)
@test hash(lim2) == hash(lim)

# Specializing to singleton limit.
d = FreeGraph{FreeCategory.Ob,FreeCategory.Hom}()
add_vertex!(d, ob=A)

d = getvalue(specialize(FreeDiagram(d)))
ThCategory.id[FreeCategory.Meta.M](A)
ThCategory.id(A)
# TODO singleton stuff
# lim = limit[M](d)
# @test ob(lim) == A

# Colimits
##########

# Colimit data structure.
f, g = Hom(:f, A, C), Hom(:g, B, C)
colim = ColimitCocone(Cospan(f,g), FreeDiagram(DD([A,B])))
@test ob(colim) == C
@test apex(colim) == C
@test legs(colim) == [f,g]

# Specializing to singleton colimit.
d = FreeGraph{FreeCategory.Ob,FreeCategory.Hom}()
add_vertex!(d, ob=A)
d = getvalue(specialize(FreeDiagram(d)))
# TODO singleton stuff
# colim = colimit(getvalue(M), d)
# @test ob(colim) == A

# Epi mono.
𝒞 = ACSetCategory(Graph())
X = @withmodel TypedCatWithCoproducts(𝒞) (⊕) begin 
  path_graph(Graph, 2) ⊕ path_graph(Graph, 2)
end
Y = @withmodel TypedCatWithCoproducts(𝒞) (⊕) begin 
  path_graph(Graph, 2) ⊕ cycle_graph(Graph, 1)
end

f = ACSetTransformation(X, Y; V=[1,2,1,2],E=[1,1])
Im = path_graph(Graph, 2)
C = Category(𝒞)
epi, mono = epi_mono(f, C)
@test is_isomorphic(codom(epi), Im)
@test is_isomorphic(image(f, C)|>apex, Im)
@test is_isomorphic(coimage(f, C)|>apex, Im)
@test is_epic(epi)
@test is_monic(mono)

end # module

