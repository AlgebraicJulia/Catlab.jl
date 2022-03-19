module TestDiagrams
using Test

using Catlab.Theories, Catlab.Graphs, Catlab.CategoricalAlgebra
using Catlab.Graphs.BasicGraphs: TheoryGraph, TheorySymmetricGraph
using Catlab.Present
import Catlab.CategoricalAlgebra.FinCats: is_natural

const SchSGraph = TheorySymmetricGraph

# Diagrams
##########

# Diagram for paths of length 2.
C = FinCat(@acset Graph begin
  V = 3
  E = 2
  src = [1,2]
  tgt = [3,3]
end)
D = FinDomFunctor([:E,:E,:V], [:tgt,:src], C, FinCat(SchSGraph))
d = Diagram(D)
@test shape(d) == C
@test ob_map(d, 3) == SchSGraph[:V]
@test hom_map(d, 1) == SchSGraph[:tgt]
@test startswith(sprint(show, d), "Diagram{id}(")

# Diagram morphisms
###################

f = DiagramHom([(2,:inv), (1,:inv), 3], [2,1], d, d)
@test dom(f) == d
@test codom(f) == d
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
@test dom(op(g)) == Diagram{co}(ιV)
@test codom(op(g)) == Diagram{co}(D)
@test op(g) == DiagramHom{co}([(1,:src)], ιV, D)
@test op(g)⋅op(f) == op(f⋅g)

# Monads of diagrams
####################

C = FinCat(TheoryGraph)
d = munit(Diagram{id}, C, :V)
@test is_discrete(shape(d))
@test only(collect_ob(diagram(d))) == TheoryGraph[:V]
f = munit(DiagramHom{id}, C, :src)
@test only(components(diagram_map(f))) == TheoryGraph[:src]

# Limits of diagrams
#########################
is_natural(D::DiagramHom) =
  is_functorial(shape_map(D)) && is_natural((diagram_map(D)))

# Nontrivial Examples
#--------------------
# FinCats
@present ArrPres_(FreeSchema) begin
  (A1, A2)::Ob; a::Hom(A1, A2)
end
@present CSpanPres_(FreeSchema) begin
  (C1, C2, C3)::Ob; c1::Hom(C1, C2); c2::Hom(C3,C2)
end
@present LoopPres_(FreeSchema) begin
  L::Ob; l::Hom(L,L)
end
@present ThFSet(FreeSchema) begin
  X::Ob
end

@acset_type FSet(ThFSet)

Arr, CSpan, Loop, FS = FinCat.([ArrPres_, CSpanPres_, LoopPres_, ThFSet])

# ACSet Cats
const ACSetCat{S} = TypeCat{S, ACSetTransformation}
const Grph = ACSetCat{Graph}
const Finset = ACSetCat{FSet}

# FinFunctors
FS_CS = FinDomFunctor(Dict(:X=>:C2), nothing, FS, CSpan)
F_AC = FinDomFunctor(Dict(:A1=>:C1, :A2=>:C2), Dict(:a=>:c1), Arr, CSpan)
G_AC = FinDomFunctor(Dict(:A1=>:C3, :A2=>:C2), Dict(:a=>:c2), Arr, CSpan)
A_L  = FinDomFunctor(Dict(:A1=>:L,:A2=>:L), Dict(:a=>:l), Arr, Loop)
F_AA = FinDomFunctor(Dict(:A1=>:A1, :A2=>:A2), Dict(:a=>:a), Arr, Arr)
H_CA = FinDomFunctor(Dict(:C1=>:A1, :C2=>:A2, :C3=>:A1),
                     Dict(:c1=>:a, :c2=>:a), CSpan, Arr)

# Graphs/Finsets
g1,g2 = Graph.([1,2])
t1 = apex(terminal(Graph))
ar = @acset Graph begin V=2; E=2; src=[1,2]; tgt=[2,2] end
f1,f2,f3,f4 = fs = [@acset FSet begin X=i end for i in 1:4]

ig1,it1 = id.([g1,t1])
if1,if2 = id.([f1,f2])
g1_arr1, g1_arr2 = homomorphisms(g1, ar)
gt1_arr1 = homomorphism(g1 ⊕ t1, ar)
t1_ar = homomorphism(t1, ar)
g12a, g12b = homomorphisms(g1, g2)
g1_gt1,g1_gt1_2 = homomorphisms(g1, g1 ⊕ t1)
ar_t1 = homomorphism(ar, t1)
g1_t1= homomorphism(g1, t1)
g21 = homomorphism(g2, g1)
g2_t1 = homomorphism(g2, t1)
ar_ar = homomorphisms(ar,ar)[2]
f12 = homomorphism(f1,f2)
f21 = homomorphism(f2,f1)
f32 = homomorphism(f3,f2)
f31 = homomorphism(f3,f1)
f22_1 = ACSetTransformation(f2,f2;X=[1,1])
f23 = ACSetTransformation(f2,f3; X=[2,2])
f13_2 = ACSetTransformation(f1,f3;X=[2])

# Diagrams to Grph or FinSet
AG_g1  = FinDomFunctor(Dict(:A1=>g1,:A2=>g1), Dict(:a=>ig1), Arr, Grph());

CG_g1t1ar = FinDomFunctor(Dict(:C1=>g1 ⊕ t1,:C2=>ar, :C3=>g1),
                          Dict(:c1=>gt1_arr1, :c2=>g1_arr2),
                          CSpan, Grph());
AG_g12 = FinDomFunctor(Dict(:A1=>g2,:A2=>g1),
                        Dict(:a=>homomorphism(g2,g1)),
                        Arr, Grph());
AG_t1 = FinDomFunctor(Dict(:A1=>t1,:A2=>t1), Dict(:a=>it1), Arr, Grph());
CG_g1 = FinDomFunctor(Dict(:C1=>g1,:C2=>g1,:C3=>g1),
                      Dict(:c1=>ig1,:c2=>ig1),
                      CSpan, Grph());
CG_t1ar = FinDomFunctor(Dict(:C1=>t1,:C2=>ar,:C3=>g1),
                        Dict(:c1=>t1_ar,:c2=>g1_arr2),
                        CSpan, Grph());
FS_ar = FinDomFunctor(Dict(:X=>ar), FS, Grph());
LG_g2 = FinDomFunctor(Dict(:L=>f2), Dict(:l=>if2), Loop, Finset());
LG_g1 = FinDomFunctor(Dict(:L=>f1), Dict(:l=>if1), Loop, Finset());
A_12  = FinDomFunctor(Dict(:A1=>f1,:A2=>f2), Dict(:a=>f12), Arr, Finset());
A_13  = FinDomFunctor(Dict(:A1=>f1,:A2=>f3), Dict(:a=>f13_2), Arr, Finset());

ds = [AG_g1, CG_g1t1ar, AG_g12, CG_g1, CG_t1ar, LG_g2, LG_g1, A_12, A_13]
AGg1, CGg1t1ar, AGg12, CGg1, CGt1ar, LGg2, LGg1, A12, A13 = Diagram.(ds)

# Diagram morphisms
F_AAg1 = DiagramHom(id(Arr), Dict(:A1=>g12a,:A2=>ig1), AG_g1, AG_g12);
G_AAg1 = DiagramHom(F_AA, Dict(:A1=>g12b, :A2=>ig1),           AG_g1, AG_g12);
H_CAg1 = DiagramHom(H_CA, Dict(:C1=>g12a, :C2=>ig1,:C3=>g12b), CG_g1, AG_g12);
F_2 = DiagramHom(F_AC, Dict(:A1=>g1_gt1, :A2=>g1_arr1), AGg1, CGg1t1ar);
G_2 = DiagramHom(G_AC, Dict(:A1=>ig1,    :A2=>g1_arr2), AGg1, CGg1t1ar);
# ACop1 = DiagramHom{op}(H_CA, Dict(:C1=>g21,:C2=>ig1, :C3=>g21), AG_g12, CG_g1)
# ACop2 = DiagramHom{op}(H_CA, Dict(:C1=>g2_t1,:C2=>g1_arr2, :C3=>g21),
#                        AG_g12, CG_t1ar)
Fop = DiagramHom{op}(F_AC, Dict(:A1=>it1, :A2=>ar_t1), CG_t1ar, AG_t1);
Gop = DiagramHom{op}(G_AC, Dict(:A1=>g1_t1,:A2=>ar_t1), CG_t1ar, AG_t1);
Hop = DiagramHom{op}(FS_CS, Dict(:X=>ar_ar),  CG_t1ar, FS_ar);
AL1 = DiagramHom(A_L, Dict(:A1=>if1,:A2=>f31),  A_13, LG_g1);
AL2 = DiagramHom(A_L, Dict(:A1=>f12, :A2=>f32),  A_13, LG_g2);
ALop1 = DiagramHom{op}(A_L, Dict(:A1=>f21,:A2=>f22_1),  LG_g2, A_12);
ALop2 = DiagramHom{op}(A_L, Dict(:A1=>f21,:A2=>f23),  LG_g2, A_13)

ALop1 = DiagramHom{op}(A_L, Dict(:A1=>f21,:A2=>f22_1),  LG_g2, A_12);
ALop2 = DiagramHom{op}(A_L, Dict(:A1=>f21,:A2=>f23),  LG_g2, A_13)
ALop3 = DiagramHom{op}(A_L, Dict(:A1=>if1,:A2=>f13_2),  LG_g1, A_13)
CA1 = DiagramHom(H_CA, Dict(:C1=>ig1, :C2=>ig1, :C3=>ig1), CGg1, AGg1)
CC1 = DiagramHom(id(CSpan), Dict(:C1=>g1_gt1_2, :C2=>g1_arr2, :C3=>ig1),
                 CGg1, CGg1t1ar);

# Limits
#-------
p1 = product([AGg1, CGg1t1ar, AGg12, CGg1, CGt1ar]);
p2 = product([LGg1, LGg2]);
e1 = equalizer(DiagramHom{id}[F_AAg1,G_AAg1]);
e2 = equalizer(DiagramHom{id}[F_2,G_2]);
pb = pullback(Multicospan([G_AAg1,H_CAg1]));

map([p1, p2, e1, e2, pb]) do lim
  @test is_functorial(diagram(apex(lim)))
  @test all(is_natural.(legs(lim)))
end

u = universal(p2, Multispan([AL1, AL2]))
@test is_natural(u)

# u = factorize(eq2, CA1) TODO equalizer universal prop in both fincats and diagrams


# Limits(op)
#-----------
p1 = product(Diagram{op}.([A_12,A_13]));
p2 = product(Diagram{op}.([AG_g1, CG_g1t1ar, AG_g12, CG_g1, CG_t1ar]));
# e = equalizer() NOT SUPPORTED - requires Kan
# pb = pullback()) NOT SUPPORTED - requires Kan
map([p1, p2]) do lim
  @test is_functorial(diagram(apex(lim)))
  @test all(is_natural.(legs(lim)))
end

u = universal(p1, Multispan([ALop1, ALop2]))
@test is_natural(u)

# Colimits
#----------
cp1 = coproduct(Diagram{id}[AGg1, CGg1]);
cp2 = coproduct(Diagram{id}[AGg1, CGg1t1ar, AGg12, CGg1, CGt1ar]);

# coequalizer()  NOT SUPPORTED - requires Kan
# pushout() NOT SUPPORTED - requires Kan
map([cp1, cp2]) do clim
  @test is_functorial(diagram(apex(clim)))
  @test all(is_natural.(legs(clim)))
end

u = universal(cp1, Multicospan([F_2,CC1]))
@test is_natural(u)

# Colimits(op)
#------------
cp1 = coproduct(Diagram{op}.([LG_g1, LG_g2]));
cp2 = coproduct(Diagram{op}.([CG_g1, CG_t1ar]));
ce = coequalizer([Fop,Gop]);
ce2 = coequalizer(DiagramHom{op}[Fop,Fop]);
po = pushout(Multispan([ALop1, ALop2]));

map([cp1, cp2, ce, ce2, po]) do clim
  @test is_functorial(diagram(apex(clim)))
  @test all(is_natural.(legs(clim)))
end

u = universal(cp1, Multicospan([ALop3, ALop2]))
@test is_natural(u)

# TODO: u = factorize(ce, ...) #

end # module
