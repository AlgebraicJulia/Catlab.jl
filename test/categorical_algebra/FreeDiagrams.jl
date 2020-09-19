module TestFreeDiagrams
using Test

using Catlab.Theories, Catlab.CategoricalAlgebra

A, B, C, D = Ob(FreeCategory, :A, :B, :C, :D)

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
@test ob(discrete) == [A,B,C]

diagram = FreeDiagram(discrete)
@test ob(diagram) == [A,B,C]
@test isempty(hom(diagram))

# Spans.
f, g = Hom(:f, C, A), Hom(:g, C, B)
span = Span(f,g)
@test apex(span) == C
@test legs(span) == [f,g]
@test feet(span) == [A,B]
@test left(span) == f
@test right(span) == g

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
@test src(diagram) == [1,1,1]
@test tgt(diagram) == [2,3,4]

# Cospans.
f, g = Hom(:f, A, C), Hom(:g, B, C)
cospan = Cospan(f,g)
@test apex(cospan) == C
@test legs(cospan) == [f,g]
@test feet(cospan) == [A,B]
@test left(cospan) == f
@test right(cospan) == g

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
@test hom(para) == [f,g,h]

diagram = FreeDiagram(para)
@test ob(diagram) == [A,B]
@test hom(diagram) == [f,g,h]
@test src(diagram) == [1,1,1]
@test tgt(diagram) == [2,2,2]

@show typeof(diagram)

function SquareDiagram(left, top, bottom, right)
    # check that the domains and codomains match
    #   1   -top->   3
    #   |            |
    # left         right
    #   v            v
    #   2  -bottom-> 4
    # this is numbered as if it were a pushout square.

    @assert codom(top) == dom(right)
    @assert dom(top) == dom(left)
    @assert dom(bottom) == codom(left)
    @assert codom(bottom) == codom(right)

    V = [dom(left), codom(left), dom(right), codom(right)]
    E = [(1,2, left), (1,3, top), (2,4, bottom), (3,4, right)] 
    return FreeDiagram(V, E)
end


function hcompose(s₁::AbstractFreeDiagram, s₂::AbstractFreeDiagram)
    #   1   -f->   3  -g->   5
    #   |          |         |
    #   |          |         |
    #   v          v         v
    #   2  -f'->   4  -g'->  6
    # 
    @assert ob(s₁)[3] == ob(s₂)[1]
    @assert ob(s₁)[4] == ob(s₂)[2]
    @assert hom(s₁)[4] == hom(s₂)[1]

    f = hom(s₁)[2]
    f′= hom(s₁)[3]
    g = hom(s₂)[2]
    g′= hom(s₂)[3]
    return SquareDiagram(hom(s₁)[1], f⋅g, f′⋅g′, hom(s₂)[end])
end

function vcompose(s₁::AbstractFreeDiagram, s₂::AbstractFreeDiagram)
    @assert ob(s₁)[2] == ob(s₂)[1]
    @assert ob(s₁)[4] == ob(s₂)[3]
    @assert hom(s₁)[3] == hom(s₂)[2]
    f = hom(s₁)[1]
    f′= hom(s₁)[4]
    g = hom(s₂)[1]
    g′= hom(s₂)[4]
    return SquareDiagram(f⋅g, hom(s₁)[2], hom(s₂)[3], f′⋅g′)
end

l, t, b, r = Hom(:lef, A,B), Hom(:top, A, C), Hom(:bot, B, D), Hom(:rht, C,D)
sq1 = SquareDiagram(l,t,b,r)
@show sq1

@test_throws AssertionError hcompose(sq1, sq1)

l, t, b, r = Hom(:lef, A,B), Hom(:top, A, A), Hom(:bot, B, B), Hom(:rht, A,B)
rr = Hom(:rr, A,B)
sq2 = SquareDiagram(l,t,b,r)
sq3 = hcompose(sq2, SquareDiagram(r, t, b, rr))
@test hom(sq3)[1] == l
@test hom(sq3)[2] == compose(t,t)
@test hom(sq3)[3] == compose(b,b)
@test hom(sq3)[4] == rr


@test_throws AssertionError vcompose(sq2, sq2)

ll = Hom(:ll, B, A)
rr = Hom(:rr, B, A)
sq4 = vcompose(sq2, SquareDiagram(ll, b, t, rr))
@test hom(sq4)[1] == compose(l, ll)
@test hom(sq4)[4] == compose(r, rr)
@test hom(sq4)[2] == t
@test hom(sq4)[3] == t

end
