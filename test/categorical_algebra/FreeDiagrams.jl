module TestFreeDiagrams
using Test

using Catlab.Theories, Catlab.CategoricalAlgebra.FreeDiagrams

A, B, C = Ob(FreeCategory, :A, :B, :C)

# General diagrams
##################

f, g, h = Hom(:f, A, C), Hom(:g, B, C), Hom(:h, A, B)
diagram = FreeDiagram([A,B,C], [(1,3,f),(2,3,g),(1,2,h)])
@test ob(diagram) == [A,B,C]
@test hom(diagram) == [f,g,h]
@test src(diagram) == [1,2,1]
@test tgt(diagram) == [3,3,2]
@test_throws Exception FreeDiagram([A,B,C], [(1,2,f),(2,3,g),(1,2,h)])

# Diagrams of fixed shape
#########################

# Spans.
f, g = Hom(:f, C, A), Hom(:g, C, B)
span = Span(f,g)
@test apex(span) == C
@test left(span) == f
@test right(span) == g

diagram = FreeDiagram(span)
@test ob(diagram) == [C,A,B]
@test hom(diagram) == [f,g]
@test src(diagram) == [1,1]
@test tgt(diagram) == [2,3]

f = Hom(:f, A, B)
@test_throws Exception Span(f,g)

# Cospans.
f, g = Hom(:f, A, C), Hom(:g, B, C)
cospan = Cospan(f,g)
@test base(cospan) == C
@test left(cospan) == f
@test right(cospan) == g

diagram = FreeDiagram(cospan)
@test ob(diagram) == [A,B,C]
@test hom(diagram) == [f,g]
@test src(diagram) == [1,2]
@test tgt(diagram) == [3,3]

# Parallel morphisms.
f, g = Hom(:f, A, B), Hom(:g, A, B)
pair = ParallelPair(f,g)
@test dom(pair) == A
@test codom(pair) == B
@test first(pair) == f
@test last(pair) == g

diagram = FreeDiagram(pair)
@test ob(diagram) == [A,B]
@test hom(diagram) == [f,g]
@test src(diagram) == [1,1]
@test tgt(diagram) == [2,2]

end
