module TestShapeDiagrams
using Test

using Catlab.Theories, Catlab.CategoricalAlgebra.ShapeDiagrams

A, B, C = Ob(FreeCategory, :A, :B, :C)

# Spans.
f, g = Hom(:f, C, A), Hom(:g, C, B)
span = Span(f,g)
@test apex(span) == C
@test left(span) == f
@test right(span) == g
f = Hom(:f, A, B)
@test_throws Exception Span(f,g)

# Cospans.
f, g = Hom(:f, A, C), Hom(:g, B, C)
cospan = Cospan(f,g)
@test base(cospan) == C
@test left(cospan) == f
@test right(cospan) == g

# Diagrams.
f, g, h = Hom(:f, A, C), Hom(:g, B, C), Hom(:h, A, B)
diag = Diagram([A,B,C],[(1,3,f),(2,3,g),(1,2,h)])
@test_throws Exception Diagram([A,B,C],[(1,2,f),(2,3,g),(1,2,h)])

end
