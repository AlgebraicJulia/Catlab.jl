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

end
