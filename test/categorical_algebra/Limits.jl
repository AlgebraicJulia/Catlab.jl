""" Tests of limits and colimits in general.

More extensive tests are provided by tests of (co)limits in specific categories
such as Set and FinSet.
"""
module TestLimits
using Test

using Catlab.Theories, Catlab.CategoricalAlgebra, Catlab.Graphs

A, B, C = Ob(FreeCategory, :A, :B, :C)

# Limits
########

# Limit data structure.
f, g = Hom(:f, C, A), Hom(:g, C, B)
lim = Limit(ObjectPair(A,B), Span(f,g))
@test lim isa BinaryProduct
@test ob(lim) == C
@test apex(lim) == C
@test legs(lim) == [f,g]

lim2 = Limit(ObjectPair(A,B), Span(Hom(:f, C, A),Hom(:g, C, B)))
@test hash(lim2) == hash(lim)


lim = Limit(DiscreteDiagram([A,B]), Span(f,g))
@test lim isa Product

# Specializing to singleton limit.
d = FreeDiagram{FreeCategory.Ob,FreeCategory.Hom}(1, ob=A)
lim = limit(d, SpecializeLimit())
@test ob(lim) == A

# Colimits
##########

# Colimit data structure.
f, g = Hom(:f, A, C), Hom(:g, B, C)
colim = Colimit(ObjectPair(A,B), Cospan(f,g))
@test colim isa BinaryCoproduct
@test ob(colim) == C
@test apex(colim) == C
@test legs(colim) == [f,g]

colim = Colimit(DiscreteDiagram([A,B]), Cospan(f,g))
@test colim isa Coproduct

# Specializing to singleton colimit.
d = FreeDiagram{FreeCategory.Ob,FreeCategory.Hom}(1, ob=A)
colim = colimit(d, SpecializeColimit())
@test ob(colim) == A

# Epi mono.
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

# Limits of FinCats
###################

# Cube, except one dimension has an involution on one terminus
@present X(FreeSchema) begin (X₀,X₁)::Ob; x::Hom(X₀,X₁) end
@present Y(FreeSchema) begin (Y₀,Y₁)::Ob; y::Hom(Y₀,Y₁) end
@present Z(FreeSchema) begin 
  (Z₀,Z₁)::Ob; z::Hom(Z₀,Z₁); 
  inv::Hom(Z₁,Z₁); compose(inv, inv) == inv 
end

π₁,π₂,π₃ = XYZ = product(FinCat.([X,Y,Z]))

@test hom_map(π₂, Symbol("(id(X₀), id(Y₁), inv)")) == id(last(Y.generators[:Ob]))
@test hom_map(π₃, Symbol("(id(X₀), id(Y₁), inv)")) == last(Z.generators[:Hom])

# 8 vertices on a cube
@test length(ob_generators(apex(XYZ))) == 8
# 12 sides of cube, plus loops on the corners of the top face 
@test length(hom_generators(apex(XYZ))) == 12+4
# 6 faces of the cube, plus equations on the four loops
# plus inv naturality squares with (x Y₀ -) (x Y₁ -) (X₀ y -) (X₁ y -)
@test length(equations(presentation(apex(XYZ)))) == 6 + 4 + 4

end
