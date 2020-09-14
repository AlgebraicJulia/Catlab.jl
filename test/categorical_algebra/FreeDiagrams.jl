module TestFreeDiagrams
using Test

using Catlab.Theories, Catlab.CategoricalAlgebra

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

# Empty diagrams.
@test isempty(EmptyDiagram{FreeCategory.Ob}())

# Object pairs.
pair = ObjectPair(A,B)
@test length(pair) == 2
@test first(pair) == A
@test last(pair) == B

# Discrete diagrams.
discrete = DiscreteDiagram([A,B,C])
@test length(discrete) == 3
A′, B′, C′ = discrete
@test [A′,B′,C′] == collect(discrete)

diagram = FreeDiagram(discrete)
@test ob(diagram) == [A,B,C]
@test isempty(hom(diagram))

# Spans.
f, g = Hom(:f, C, A), Hom(:g, C, B)
span = Span(f,g)
@test apex(span) == C
@test legs(span) == [f,g]
@test left(span) == f
@test right(span) == g

f = Hom(:f, A, B)
@test_throws Exception Span(f,g)

# Multispans.
f, g, h = Hom(:f, C, A), Hom(:g, C, B), Hom(:h, C, A)
span = Multispan([f,g,h])
@test apex(span) == C
@test legs(span) == [f,g,h]

diagram = FreeDiagram(span)
@test ob(diagram) == [C,A,B,A]
@test hom(diagram) == [f,g,h]
@test src(diagram) == [1,1,1]
@test tgt(diagram) == [2,3,4]

# Cospans.
f, g = Hom(:f, A, C), Hom(:g, B, C)
cospan = Cospan(f,g)
@test base(cospan) == C
@test legs(cospan) == [f,g]
@test left(cospan) == f
@test right(cospan) == g

# Multicospans.
f, g, h = Hom(:f, A, C), Hom(:g, B, C), Hom(:h, A, C)
cospan = Multicospan([f,g,h])
@test base(cospan) == C
@test legs(cospan) == [f,g,h]

diagram = FreeDiagram(cospan)
@test ob(diagram) == [A,B,A,C]
@test hom(diagram) == [f,g,h]
@test src(diagram) == [1,2,3]
@test tgt(diagram) == [4,4,4]

# Parallel pairs.
f, g = Hom(:f, A, B), Hom(:g, A, B)
pair = ParallelPair(f,g)
@test dom(pair) == A
@test codom(pair) == B
@test first(pair) == f
@test last(pair) == g

# Parallel morphisms.
f, g, h = Hom(:f, A, B), Hom(:g, A, B), Hom(:h, A, B)
para = ParallelMorphisms([f,g,h])
@test dom(para) == A
@test codom(para) == B

diagram = FreeDiagram(para)
@test ob(diagram) == [A,B]
@test hom(diagram) == [f,g,h]
@test src(diagram) == [1,1,1]
@test tgt(diagram) == [2,2,2]

end
