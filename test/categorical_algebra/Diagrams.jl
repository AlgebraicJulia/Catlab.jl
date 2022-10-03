module TestDiagrams

using Test

using Catlab.Theories, Catlab.Graphs, Catlab.CategoricalAlgebra, Catlab.Present

const SchSGraph = SchSymmetricGraph

# Diagrams
##########

# Diagram for paths of length 2.
C = FinCat(@acset Graph begin V = 3; E = 2; src = [1,2]; tgt = [3,3] end)
D = FinDomFunctor([:E,:E,:V], [:tgt,:src], C, FinCat(SchSGraph))


d = Diagram(D)
@test shape(d) == C
@test ob_map(d, 3) == SchSGraph[:V]
@test hom_map(d, 1) == SchSGraph[:tgt]
@test first.(collect_ob(d)) == [:E,:E,:V]
@test first.(collect_hom(d)) == [:tgt,:src]
@test startswith(sprint(show, d), "Diagram{id}(")
@test hash(D) != hash(Diagram{op}(D))

# Diagram morphisms
###################

f = DiagramHom([(2,:inv), (1,:inv), 3], [2,1], d, d)
@test dom(f) == d
@test codom(f) == d
@test hash(f) == hash(DiagramHom([(2,:inv), (1,:inv), 3], [2,1], d, d))
@test is_functorial(shape_map(f))
@test shape_map(f) == FinFunctor([2,1,3], [2,1], C, C)
ϕ = diagram_map(f)
@test is_natural(ϕ, check_equations=false)
@test ϕ[1] == SchSGraph[:inv]
@test ϕ[3] == id(SchSGraph[:V])
@test ob_map(f, 2) == (1, SchSGraph[:inv])
@test hom_map(f, 2) == Path(graph(C), 1)
@test collect_ob(f) == [(2, ϕ[1]), (1, ϕ[2]), (3, ϕ[3])]
@test collect_hom(f) == [Path(graph(C), 2), Path(graph(C), 1)]
f² = f⋅f
@test shape_map(f²) == FinFunctor(1:3, 1:2, C, C)
@test hash(f) != hash(f²)

f = DiagramHom{op}([(2,:inv), (1,:inv), 3], [2,1], D, D)
ιV = FinDomFunctor([:V], FinCat(1), FinCat(SchSGraph))
g = DiagramHom{op}([(1,:src)], D, ιV)
@test dom(g) == Diagram{op}(D)
@test codom(g) == Diagram{op}(ιV)
@test compose(id(dom(g)), g) == g
@test compose(g, id(codom(g))) == g
@test is_natural(diagram_map(g))
@test startswith(sprint(show, f), "DiagramHom{op}(")

fg = f⋅g
@test ob_map(fg, 1) == (2, SchSGraph[:inv]⋅SchSGraph[:src])

d = dom(f)
@test op(op(d)) == d
@test op(op(f)) == f
@test dom(op(f)) == op(codom(f))
@test codom(op(f)) == op(dom(f))
@test op(g)⋅op(f) == op(f⋅g)

# Morphism search
##################

# Diagrams in a FinCat

"""
Shapes:       •         •
              ↓    ==>  ↓
              •         •

living        1 --> 2
over          |     |
square:       v     v
              3 --> 4
A diagram morphism in the forward direction is equivalent to a
natural transformation. When the shape map is identity, this is
the calculation of FinTransformations into Squarish, as found in the FinCats test suite. However, there are also shape maps which
send  both objects to the first or the second object. Only in the
second case does there exist a diagram morphism.

"""
Sq = @acset(Graph, begin V=4;E=4;src=[1,1,2,3]; tgt=[2,3,4,4] end)
Squarish = FinCatGraph(Sq, [[[1,3],[2,4]]])

Arr = FinCat(path_graph(Graph, 2))
XF = FinFunctor((V=[1,3], E=[[2]]), Arr, Squarish)
XG = FinFunctor((V=[2,4], E=[[3]]), Arr, Squarish)
@test all(is_functorial,[XF,XG])
F, G = Diagram.([XF,XG])
hs = homomorphisms(F,G)
@test length(hs) == 2
@test length(homomorphisms(F,G; monic_obs=true))==1

# There are no morphisms from RHS to LHS, so there are no op functors
@test isempty(homomorphisms((Diagram{op}.([XF,XG]))...))

# But if we look for op morphisms from the RHS *to* the LHS, we get 2
# one of which has id shape map and the other which send both objs to 1.
hs = homomorphisms((Diagram{op}.([XG,XF]))...)
@test length(hs) == 2
@test length(homomorphisms((Diagram{op}.([XG,XF]))...; monic_obs=true))==1

# Diagrams in C-Set

# dots shapes are just C-Sets
@present SchDot(FreeSchema) begin X::Ob end
toDot(x::StructACSet) = FinDomFunctor(Dict(:X=>x), nothing, FinCat(SchDot), ACSetCat{typeof(x)}())
ar = path_graph(Graph, 2)
g1 = toDot(ar)
g2 = toDot(Sq)
@test length(homomorphisms(g1,g2)) == length(homomorphisms(ar,Sq))

# more complicated shapes

const Grph = ACSetCat{Graph}
@present SchArr(FreeSchema) begin (A,B)::Ob; f::Hom(A,B) end
Arr = FinCat(SchArr)
A,B = SchArr.generators[:Ob]

toArr(f::ACSetTransformation) = FinDomFunctor(
  Dict(:A=>dom(f), :B=>codom(f)),
  Dict(:f=>f),
  Arr, ACSetCat{typeof(dom(f))}())
f1 = toArr(homomorphism(Graph(1), Graph(2)))
f2 = toArr(homomorphism(Graph(2), Graph(1)))

res = homomorphisms(f1,f2)
@test length(res) == 2

trm = terminal(Graph) |> apex
f1 = toArr(homomorphism(Graph(2), ar; monic=true))
f2 = toArr(homomorphism(Graph(2), trm ⊕ trm; monic=true))
res = homomorphisms(f1,f2)
@test length(res) == 2

twoC, fourC =  [cycle_graph(Graph, i) for i in [2,4]]
otherG = @acset Graph begin V=2; E=3; src=[1,1,2]; tgt=[1,2,1] end
xF = FinDomFunctor(Dict(:A=>ar,:B=>fourC), Dict(:f=>homomorphism(ar,fourC)),
                   Arr, Grph())
xG = FinDomFunctor(Dict(:A=>twoC,:B=>otherG),
                   Dict(:f=>homomorphism(twoC,otherG;monic=true)),
                   Arr, Grph())
@test all(is_functorial, [xF,xG])
F,G=Diagram.([xF,xG]);
res = homomorphisms(F,G; diag_kws=(monic=Symbol.(["(A, V)"]),));


# Monads of diagrams
####################

C = FinCat(SchGraph)
d = munit(Diagram{id}, C, :V)
@test is_discrete(shape(d))
@test only(collect_ob(d)) == SchGraph[:V]
f = munit(DiagramHom{id}, C, :src)
@test only(components(diagram_map(f))) == SchGraph[:src]

end
