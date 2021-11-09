module TestFreeDiagrams
using Test

using Catlab.Theories, Catlab.Graphs, Catlab.CategoricalAlgebra

A, B, C, D = Ob(FreeCategory, :A, :B, :C, :D)

# Diagrams of flexible shape
############################

# FinDomFunctors
#---------------

f, g, h = Hom(:f, A, C), Hom(:g, B, C), Hom(:h, A, B)
J = FinCat(parallel_arrows(Graph, 2))
F = FinDomFunctor([A, C], [f, h⋅g], J)
@test is_functorial(F)
@test diagram_type(F) <: Tuple{FreeCategory.Ob,FreeCategory.Hom}
@test cone_objects(F) == [A, C]
@test cocone_objects(F) == [A, C]

diagram = FreeDiagram(ParallelPair(f, h⋅g))
@test FreeDiagram(F) == diagram
F = FinDomFunctor(diagram)
@test dom(F) isa FinCat
@test codom(F) isa TypeCat{<:FreeCategory.Ob,<:FreeCategory.Hom}
@test ob_map(F, 1) == A
@test hom_map(F, 2) == h⋅g
@test collect_ob(F) == [A, C]
@test collect_hom(F) == [f, h⋅g]

# Free diagrams
#--------------

diagram = FreeDiagram([A,B,C], [(f,1,3),(g,2,3),(h,1,2)])
@test diagram_type(diagram) <: Tuple{FreeCategory.Ob,FreeCategory.Hom}
@test ob(diagram) == [A,B,C]
@test hom(diagram) == [f,g,h]
@test (src(diagram), tgt(diagram)) == ([1,2,1], [3,3,2])
@test_throws Exception FreeDiagram([A,B,C], [(f,1,2),(g,2,3),(h,1,2)])

# Bipartite free diagrams
#------------------------

bd = BipartiteFreeDiagram([A,B], [C], [(f,1,1),(g,2,1)])
@test diagram_type(diagram) <: Tuple{FreeCategory.Ob,FreeCategory.Hom}
@test (ob₁(bd), ob₂(bd)) == ([A,B], [C])
@test hom(bd) == [f,g]
@test (src(bd), tgt(bd)) == ([1,2], [1,1])
@test FreeDiagram(bd) == FreeDiagram([A,B,C], [(f,1,3),(g,2,3)])

as_basic_bipartite(diagram::BipartiteFreeDiagram{Ob,Hom}) where {Ob,Hom} =
  (d = BipartiteFreeDiagram{Ob,Hom}(); copy_parts!(d, diagram); d)

# Diagrams of fixed shape
#########################

# Empty diagrams.
@test isempty(EmptyDiagram{FreeCategory.Ob}())

# Object pairs.
pair = ObjectPair(A,B)
@test diagram_type(pair) <: Tuple{FreeCategory.Ob,Any}
@test length(pair) == 2
@test (first(pair), last(pair)) == (A, B)
pair = ObjectPair(A, B, FreeCategory.Hom)
@test diagram_type(pair) <: Tuple{FreeCategory.Ob,FreeCategory.Hom}

# Discrete diagrams.
discrete = DiscreteDiagram([A,B,C])
@test length(discrete) == 3
@test ob(discrete) == [A,B,C]

diagram = FreeDiagram(discrete)
@test ob(diagram) == [A,B,C]
@test isempty(hom(diagram))
@test BipartiteFreeDiagram(discrete, colimit=false) ==
  as_basic_bipartite(BipartiteFreeDiagram(diagram, colimit=false))
@test BipartiteFreeDiagram(discrete, colimit=true) ==
  as_basic_bipartite(BipartiteFreeDiagram(diagram, colimit=true))

# Spans.
f, g = Hom(:f, C, A), Hom(:g, C, B)
span = Span(f,g)
@test apex(span) == C
@test legs(span) == [f,g]
@test feet(span) == [A,B]
@test (left(span), right(span)) == (f, g)

f = Hom(:f, A, A)
@test legs(Span(id(A), f)) == [id(A),f]

f = Hom(:f, A, B)
@test_throws ErrorException Span(f,g)

# Multispans.
f, g, h = Hom(:f, C, A), Hom(:g, C, B), Hom(:h, C, A)
span = Multispan([f,g,h])
@test apex(span) == C
@test legs(span) == [f,g,h]
@test feet(span) == [A,B,A]

diagram = FreeDiagram(span)
@test ob(diagram) == [C,A,B,A]
@test hom(diagram) == [f,g,h]
@test (src(diagram), tgt(diagram)) == ([1,1,1], [2,3,4])

diagram = BipartiteFreeDiagram(span)
@test (ob₁(diagram), ob₂(diagram)) == ([C], [A,B,A])
@test hom(diagram) == [f,g,h]
@test (src(diagram), tgt(diagram)) == ([1,1,1], [1,2,3])
@test diagram == as_basic_bipartite(BipartiteFreeDiagram(FreeDiagram(span)))

span = Multispan([ id(FinSet(2)) for i in 1:3 ])
span = bundle_legs(span, [1, (2,3)])
@test apex(span) == FinSet(2)
@test codom.(legs(span)) == [FinSet(2), FinSet(4)]

# Cospans.
f, g = Hom(:f, A, C), Hom(:g, B, C)
cospan = Cospan(f,g)
@test apex(cospan) == C
@test legs(cospan) == [f,g]
@test feet(cospan) == [A,B]
@test (left(cospan), right(cospan)) == (f, g)

f = Hom(:f, A, A)
@test legs(Cospan(f, id(A))) == [f,id(A)]

f = Hom(:f, A ,B)
@test_throws ErrorException Cospan(f,g)

# Multicospans.
f, g, h = Hom(:f, A, C), Hom(:g, B, C), Hom(:h, A, C)
cospan = Multicospan([f,g,h])
@test apex(cospan) == C
@test legs(cospan) == [f,g,h]
@test feet(cospan) == [A,B,A]

diagram = FreeDiagram(cospan)
@test ob(diagram) == [A,B,A,C]
@test hom(diagram) == [f,g,h]
@test (src(diagram), tgt(diagram)) == ([1,2,3], [4,4,4])

diagram = BipartiteFreeDiagram(cospan)
@test (ob₁(diagram), ob₂(diagram)) == ([A,B,A], [C])
@test hom(diagram) == [f,g,h]
@test (src(diagram), tgt(diagram)) == ([1,2,3], [1,1,1])
@test diagram == as_basic_bipartite(BipartiteFreeDiagram(FreeDiagram(cospan)))

cospan = Multicospan([FinFunction([i],3) for i in 1:3])
cospan = bundle_legs(cospan, [(1,3), 2])
@test apex(cospan) == FinSet(3)
@test legs(cospan) == [FinFunction([1,3], 3), FinFunction([2], 3)]

# Parallel pairs.
f, g = Hom(:f, A, B), Hom(:g, A, B)
pair = ParallelPair(f,g)
@test (dom(pair), codom(pair)) == (A, B)
@test (first(pair), last(pair)) == (f, g)

# Parallel morphisms.
f, g, h = Hom(:f, A, B), Hom(:g, A, B), Hom(:h, A, B)
para = ParallelMorphisms([f,g,h])
@test (dom(para), codom(para)) == (A, B)
@test hom(para) == [f,g,h]

diagram = FreeDiagram(para)
@test ob(diagram) == [A,B]
@test hom(diagram) == [f,g,h]
@test (src(diagram), tgt(diagram)) == ([1,1,1], [2,2,2])

diagram = BipartiteFreeDiagram(para)
@test (ob₁(diagram), ob₂(diagram)) == ([A], [B])
@test hom(diagram) == [f,g,h]
@test (src(diagram), tgt(diagram)) == ([1,1,1], [1,1,1])
@test diagram == as_basic_bipartite(BipartiteFreeDiagram(FreeDiagram(para)))

# Composable pairs.
f, g = Hom(:f, A, B), Hom(:g, B, C)
pair = ComposablePair(f,g)
@test (dom(pair), codom(pair)) == (A, C)
@test (first(pair), last(pair)) == (f, g)
@test_throws ErrorException ComposablePair(f,f)

# Composable morphisms.
f, g, h = Hom(:f, A, B), Hom(:g, B, C), Hom(:h, C, D)
comp = ComposableMorphisms([f,g,h])
@test (dom(comp), codom(comp)) == (A, D)
@test hom(comp) == [f,g,h]

diagram = FreeDiagram(comp)
@test ob(diagram) == [A,B,C,D]
@test hom(diagram) == [f,g,h]
@test (src(diagram), tgt(diagram)) == (1:3, 2:4)

end
