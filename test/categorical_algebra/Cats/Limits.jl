""" Tests of limits and colimits in general.

More extensive tests are provided by tests of (co)limits in specific categories
such as Set and FinSet.
"""
module TestLimits

using Test, Catlab

A, B, C = Ob(FreeCategory, :A, :B, :C)
const M = Category(TypeCat(FreeCategory.Meta.M()))

# Limits
########
DD(x) = DiscreteDiagram(x)
# Limit data structure.
f, g = Hom(:f, C, A), Hom(:g, C, B)
dia = DD([A,B])
lim = Limit(Diagram(dia, M), Span(f,g))
@test ob(lim) == C
@test apex(lim) == C
@test legs(lim) == [f,g]

lim2 = Limit(Diagram(DD([A,B]), M), Span(Hom(:f, C, A),Hom(:g, C, B)))
@test hash(lim2) == hash(lim)

# Specializing to singleton limit.
d = FreeDiagram{FreeCategory.Ob,FreeCategory.Hom}()
add_vertex!(d, ob=A)
specialize(d; colimit=false)
lim = limit(specialize(d; colimit=false), M)
@test ob(lim) == A

# Colimits
##########

# Colimit data structure.
f, g = Hom(:f, A, C), Hom(:g, B, C)
colim = Colimit(Diagram(DD([A,B]),M), Cospan(f,g))
@test ob(colim) == C
@test apex(colim) == C
@test legs(colim) == [f,g]

# Specializing to singleton colimit.
d = FreeDiagram{FreeCategory.Ob,FreeCategory.Hom}()
add_vertex!(d, ob=A)
colim = colimit(specialize(d), M)
@test ob(colim) == A

# Epi mono.
if false # TODO - uncomment once CSets is working 
  X = path_graph(Graph, 2) ⊕ path_graph(Graph, 2)
  Y = path_graph(Graph, 2) ⊕ apex(terminal(Graph))
  f = ACSetTransformation(X, Y; V=[1,2,1,2],E=[1,1])
  Im = path_graph(Graph, 2)
  epi, mono = epi_mono(f)
  @test is_isomorphic(codom(epi), Im)
  @test is_isomorphic(image(f)|>apex, Im)
  @test is_isomorphic(coimage(f)|>apex, Im)
  @test is_epic(epi)
  @test is_monic(mono)
end 

end # module

