module TestFreeDiagrams

using Test, ACSets, Catlab

const T = (FreeCategory.Ob, FreeCategory.Hom)

A, B, C, D = Ob(FreeCategory, :A, :B, :C, :D)

# Diagrams of fixed shape
#########################

# Empty diagrams.
@test isempty(EmptyDiagram{FreeCategory.Ob}())

# Object pairs.
pair = ObjectPair(A,B)
@test diagram_type(FreeDiagram(pair)) == (FreeCategory.Ob{:generator}, Union{})
@test length(pair) == 2
@test (first(pair), last(pair)) == (A, B)

# Discrete diagrams.
discrete = DiscreteDiagram([A,B,C])
@test length(discrete) == 3
@test objects(discrete) == [A,B,C]

as_basic_bipartite(diagram::BipartiteFreeDiagram{Ob,Hom}) where {Ob,Hom} =
  (d = BipartiteFreeDiagram{Ob,Hom}(); copy_parts!(d, diagram); d)

diagram = FreeDiagram(discrete)
@test collect(ob(diagram)) == [A,B,C]
@test isempty(hom(diagram))
@test BipartiteFreeDiagram(discrete, colimit=false) ==
  as_basic_bipartite(BipartiteFreeDiagram(discrete, colimit=false))
@test BipartiteFreeDiagram(discrete, colimit=true) ==
  as_basic_bipartite(BipartiteFreeDiagram(discrete, colimit=true))

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

bfd = BipartiteFreeDiagram(span)
@test (ob₁(bfd), ob₂(bfd)) == ([C], [A,B,A])
diagram = FreeDiagram(bfd)
@test hom(diagram) == [f,g,h]
@test (src(diagram), tgt(diagram)) == ([1,1,1], [2,3,4])
@test bfd == as_basic_bipartite(BipartiteFreeDiagram(diagram))


# UNCOMMENT LATER OR MOVE TO SetCats folder
# span = Multispan{AbsSet,SetFunction}([ SetFunction(FinSet(2)) for i in 1:3 ])
# span = bundle_legs(span, [1, (2,3)], SetC()) 
# @test apex(span) == FinSet(2)
# @test codom.(legs(span)) == [FinSet(2), FinSet(4)]

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
@test collect(ob(diagram)) == [C, A,B,A]
@test collect(hom(diagram)) == [f,g,h]
@test (src(diagram), tgt(diagram)) == ([2,3,4], [1,1,1])

bfd = BipartiteFreeDiagram(cospan)
@test (ob₁(bfd), ob₂(bfd)) == ([A,B,A], [C])
diagram = FreeDiagram(bfd)
@test collect(hom(diagram)) == [f,g,h]
@test (src(diagram), tgt(diagram)) == ([1,2,3], [4,4,4])
@test bfd == as_basic_bipartite(BipartiteFreeDiagram(FreeDiagram(cospan)))

# MOVE TO SETCATS TEST?
# cospan = Multicospan{AbsSet, SetFunction}([FinFunction([i],3) for i in 1:3])
# cospan = bundle_legs(cospan, [(1,3), 2], SetC())
# @test apex(cospan) == FinSet(3)
# @test legs(cospan) == [FinFunction([1,3], 3), FinFunction([2], 3)]

# Parallel pairs.
f, g = Hom(:f, A, B), Hom(:g, A, B)
pair = ParallelPair(f,g)
@test (dom(pair), codom(pair)) == (A, B)
@test (first(pair), last(pair)) == (f, g)

# Parallel morphisms.
f, g, h = Hom(:f, A, B), Hom(:g, A, B), Hom(:h, A, B)
para = ParallelMorphisms([f,g,h])
@test (dom(para), codom(para)) == (A, B)
@test collect(para) == [f,g,h]

diagram = FreeDiagram(para)
@test collect(ob(diagram)) == [A,B]
@test hom(diagram) == [f,g,h]
@test (src(diagram), tgt(diagram)) == (Bool[1,1,1], Bool[0,0,0])

bfd = BipartiteFreeDiagram(para)
@test (ob₁(bfd), ob₂(bfd)) == ([A], [B])
diagram = FreeDiagram(bfd)
@test collect(hom(diagram)) == [f,g,h]
@test (src(diagram), tgt(diagram)) == ([1,1,1], [2,2,2])
@test bfd == as_basic_bipartite(BipartiteFreeDiagram(FreeDiagram(para)))

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
@test collect(comp) == [f,g,h]

diagram = FreeDiagram(comp)
@test ob(diagram) == [A,B,C,D]
@test hom(diagram) == [f,g,h]
@test (src(diagram), tgt(diagram)) == (1:3, 2:4)


# Diagrams of flexible shape
############################

# FinDomFunctors
#---------------
if false # FinDomFunctor defined after FreeDiagram?
f, g, h = Hom(:f, A, C), Hom(:g, B, C), Hom(:h, A, B)
J = FinCat(parallel_arrows(Graph, 2))
F = FinDomFunctor([A, C], [f, h⋅g], J)
@test is_functorial(F)
@test diagram_type(F) <: Tuple{FreeCategory.Ob,FreeCategory.Hom}
@test cone_objects(F) == [A, C]
@test cocone_objects(F) == [A, C]

diagram = FreeDiagram{FreeCategory.Ob{:generator},FreeCategory.Hom}(
  ParallelPair(f, h⋅g))
@test FreeDiagram(F) == diagram
F = FinDomFunctor(diagram)
@test dom(F) isa FinCat
@test codom(F) isa TypeCat{<:FreeCategory.Ob,<:FreeCategory.Hom}
@test ob_map(F, 1) == A
@test hom_map(F, 2) == h⋅g
@test collect_ob(F) == [A, C]
@test collect_hom(F) == [f, h⋅g]
end 

# Free diagrams
#--------------
f, g, h = Hom(:f, A, C), Hom(:g, B, C), Hom(:h, A, B)

diagram = FreeGraph([A,B,C], [(f,1,3),(g,2,3),(h,1,2)]) |> FreeDiagram
@test diagram_type(diagram) == (FreeCategory.Ob{:generator},FreeCategory.Hom{:generator})
@test collect(ob(diagram)) == [A,B,C]
@test collect(hom(diagram)) == [f,g,h]
@test (src(diagram), tgt(diagram)) == ([1,2,1], [3,3,2])
@test_throws Exception FreeDiagram([A,B,C], [(f,1,2),(g,2,3),(h,1,2)])

# Bipartite free diagrams
#------------------------

bd = BipartiteFreeDiagram([A,B], [C], [(f,1,1),(g,2,1)])
diagram = bd |> FreeDiagram
@test diagram_type(diagram) == (FreeCategory.Ob{:generator},FreeCategory.Hom{:generator})
@test (ob₁(bd), ob₂(bd)) == ([A,B], [C])
@test collect(hom(diagram)) == [f,g]
@test (src(bd), tgt(bd)) == ([1,2], [1,1])
# What is going on here?
# @test FreeDiagram(bd) == FreeDiagram([A,B,C], [(f,1,3),(g,2,3)])


end # module
