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
@test hash(D) == hash(D)
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

# Left Kan
##########

# Left Kan of diagram in Set (see example docs in test/Chase.jl)
#---------------------------------------------------------------
@present ThSchool′(FreeSchema) begin
  (TA′, Student′, Faculty′)::Ob
  t_s′::Hom(TA′, Student′)
  t_f′::Hom(TA′, Faculty′)
end

@present ThSchool(FreeSchema) begin
  (TA, Student, Faculty, Person)::Ob
  t_s::Hom(TA, Student)
  t_f::Hom(TA, Faculty)
  s_p::Hom(Student, Person)
  f_p::Hom(Faculty, Person)

  compose(t_s, s_p) == compose(t_f, f_p)
end

SchoolC, SchoolC′ = FinCat.([ThSchool, ThSchool′])
@acset_type School′(ThSchool′)
@acset_type School(ThSchool)

F = FinFunctor(Dict(:TA′=>:TA, :Faculty′=>:Faculty, :Student′=>:Student),
               Dict(:t_s′=>:t_s,:t_f′=>:t_f), SchoolC′, SchoolC)

I = @acset School′ begin
  TA′=2; Student′=4; Faculty′=5
  t_s′=[1,2]; t_f′=[1,2]
end

lk = leftkan(F, I, :School)
@test is_natural(lk)

expected = @acset School begin
  TA = 2; Student = 4; Faculty = 5; Person = 7
  t_s = [1,2]; t_f = [1,2]; s_p = [1,2,3,4]; f_p = [1,2,5,6,7]
end

@test is_isomorphic(expected, School(diagram(codom(lk))))

# Left kan of Diagrams in Grph
#-----------------------------

const Grph = ACSetCat{Graph}

# Set up example shape categories
@present ThArr(FreeSchema) begin
  (A,B)::Ob; f::Hom(A,B)
end
@present ThArr2(FreeSchema) begin
  (C,D)::Ob; m::Hom(C,D); n::Hom(D, C); compose(m,n) == id(C)
end
@present ThInv(FreeSchema) begin
  (Y)::Ob; f::Hom(Y,Y); compose(f,f) == id(Y)
end
@present ThOne(FreeSchema) begin
  (X)::Ob
end

@present ThInv2(FreeSchema) begin
  (Y)::Ob; f::Hom(Y,Y); compose(f,f) == f
end

pres_to_eds(ThInv2, :Inv2) # example of an equation with a :generator term


Arr, Arr2, One, Inv = FinCat.([ThArr, ThArr2, ThOne, ThInv])

# Set up graph data
two = path_graph(Graph, 2)
ar = @acset Graph begin V=2; E=2; src=[1,2]; tgt=[2,2] end
h1, h2 = homomorphisms(two, ar) # don't send both vertices to #2, or do that

# Freely adding a right inverse to a C-set transformation: f: A->B
#-----------------------------------------------------------------
F = FinFunctor(Dict(:A=>:C, :B=>:D), Dict(:f=>:m), Arr, Arr2)
# This may require adding things to A. These must then be mapped to B in a
# distinct place, thereby adding to B, too.
I = FinDomFunctor(Dict(:A=>two,:B=>ar),Dict(:f=>h1),Arr,Grph())
lk = diagram(codom(leftkan(F, I, :X; verbose=false)))
# This homomorphism is injective on vertices. Those can be easily inverted.
# However, V2 in the codomain has a self loop not present in V2 of the domain.
# Therefore the domain has an extra loop added to it.
@test ob_map(lk, :C) == ar
# The new edge ISN'T forced to match to the self loop in the codomain, though
@test ob_map(lk, :D) == @acset Graph begin V=2; E=3; src=[1,2,2]; tgt=2 end

# This homomorphism sends V1 and V2 to V2 of the codomain.
I = FinDomFunctor(Dict(:A=>two,:B=>ar),Dict(:f=>h2),Arr,Grph())
lk2 = diagram(codom(leftkan(F, I, :X2; verbose=false)))
@test is_isomorphic(ob_map(lk2, :C), ar)
# TODO: rationalize why this is the result, if it's correct
@test ob_map(lk2, :D) == @acset Graph begin V=3; E=3; src=[1,3,2]; tgt=3 end

# Freely adding an involution
#----------------------------
F = FinFunctor(Dict(:X=>:Y),nothing,One,Inv)
# creates a copy of the starting graph, and the involution is a swap function.
I = FinDomFunctor(Dict(:X=>two), nothing, One, Grph())
lk3_ = leftkan(F, I, :XF; verbose=false)
lk3 = diagram(codom(lk3_))
@test ob_map(lk3, :Y) == two ⊕ two
@test collect(hom_map(lk3, :f)[:V]) == [3,4,1,2]
@test collect(hom_map(lk3, :f)[:E]) == [2,1]

otherF = FinDomFunctor(Dict(:Y=>two), Dict(:f => id(two)), Inv, Grph())
otherD = DiagramHom(F, Dict(:X=>id(two)), Diagram(I), Diagram(otherF))
phi = lk_universal(lk3_, otherD)
@test is_natural(phi)

# Limits of diagrams
#########################

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
const Grph = ACSetCat{Graph}
const Finset = ACSetCat{FSet}

# FinFunctors
FS_CS = FinDomFunctor(Dict(:X=>:C2), nothing, FS, CSpan)
FS_A = FinDomFunctor(Dict(:X=>:A2), nothing, FS, Arr)
F_AC = FinDomFunctor(Dict(:A1=>:C1, :A2=>:C2), Dict(:a=>:c1), Arr, CSpan)
G_AC = FinDomFunctor(Dict(:A1=>:C3, :A2=>:C2), Dict(:a=>:c2), Arr, CSpan)
A_L  = FinDomFunctor(Dict(:A1=>:L,:A2=>:L), Dict(:a=>:l), Arr, Loop)
H_CA = FinDomFunctor(Dict(:C1=>:A1, :C2=>:A2, :C3=>:A1),
                     Dict(:c1=>:a, :c2=>:a), CSpan, Arr)

# Graphs/Finsets
g0,g1,g2 = Graph.([0,1,2])
t1 = apex(terminal(Graph))
arr = path_graph(Graph, 2)
ar = @acset Graph begin V=2; E=2; src=[1,2]; tgt=[2,2] end
f1,f2,f3,f4 = fs = [@acset FSet begin X=i end for i in 1:4]

ig1,it1 = id.([g1,t1])
if1,if2 = id.([f1,f2])
g1_arr1, g1_arr2 = homomorphisms(g1, ar)
harr = homomorphisms(arr,ar)[2]
g1arr = homomorphisms(g1,arr)[1]
gt1_arr1 = homomorphism(g1 ⊕ t1, ar)
t1_plus = homomorphism(t1, g1 ⊕ t1)
t1_ar = homomorphism(t1, ar)
g12a, g12b = homomorphisms(g1, g2)
g1_gt1,g1_gt1_2 = homomorphisms(g1, g1 ⊕ t1)
ar_t1 = homomorphism(ar, t1)
g1_t1= homomorphism(g1, t1)
g21 = homomorphism(g2, g1)
g01 = homomorphism(g0, g1)
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
A_01  = FinDomFunctor(Dict(:A1=>g0,:A2=>g1), Dict(:a=>g01), Arr, Grph());

ds = [AG_g1, CG_g1t1ar, AG_g12, CG_g1, CG_t1ar, LG_g2, LG_g1, A_12, A_13, A_01, AG_t1]
AGg1, CGg1t1ar, AGg12, CGg1, CGt1ar, LGg2, LGg1, A12, A13, A01, AGt1 = Diagram.(ds)

# Diagram morphisms
F_AAg1 = DiagramHom(id(Arr), Dict(:A1=>g12a,:A2=>ig1), AG_g1, AG_g12);
G_AAg1 = DiagramHom(id(Arr), Dict(:A1=>g12b, :A2=>ig1),           AG_g1, AG_g12);
H_CAg1 = DiagramHom(H_CA, Dict(:C1=>g12a, :C2=>ig1,:C3=>g12b), CG_g1, AG_g12);
F_2 = DiagramHom(F_AC, Dict(:A1=>g1_gt1, :A2=>g1_arr1), AGg1, CGg1t1ar);
G_2 = DiagramHom(G_AC, Dict(:A1=>ig1,    :A2=>g1_arr2), AGg1, CGg1t1ar);
H_2 = DiagramHom(id(Arr), Dict(:A1=>g1_t1,    :A2=>g1_t1), AGg1, AGt1)
AA_02 = DiagramHom(id(Arr), Dict(:A1=>g01, :A2=>ig1), A01, AGg1);
# ACop1 = DiagramHom{op}(H_CA, Dict(:C1=>g21,:C2=>ig1, :C3=>g21), AG_g12, CG_g1)
# ACop2 = DiagramHom{op}(H_CA, Dict(:C1=>g2_t1,:C2=>g1_arr2, :C3=>g21),
#                        AG_g12, CG_t1ar)
Fop = DiagramHom{op}(F_AC, Dict(:A1=>it1, :A2=>ar_t1), CG_t1ar, AG_t1);
Gop = DiagramHom{op}(G_AC, Dict(:A1=>g1_t1,:A2=>ar_t1), CG_t1ar, AG_t1);
Hop = DiagramHom{op}(FS_CS, Dict(:X=>ar_ar),  CG_t1ar, FS_ar);
Qop = DiagramHom{op}(FS_A, Dict(:X=>t1_ar), AG_t1, FS_ar)

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
if false
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

u = factorize(e1, AA_02)
@test is_natural(u)

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

ceq = coequalizer(DiagramHom{id}[F_2,G_2])
po = pushout(Multispan([F_2,H_2]))

""" Worked out pushout for two diagram homs in Grph:

Pushout at shape level is id(•) +. Arrow = Arrow. If we plug in the graphs:

                 •↦ V₁
                 (l1)        V₁₂ ↦ V₂
           {[•]}  ⇒  {[•₁ → •₂]  ⟶  [•₁ → •₂↺]}
   •↦ V₁ (l2)⇓
         {[•₁ → •₂↺]}

This results in a diagram with shape •→•. The first graph is the same as
before with an extra l2 component glued onto V₁, while the second graph has the
l2 component glued onto V₂. Result:

   •₂       V₁₂ ↦ V₂
   ↑         V₃ ↦ V₃
   •₁ → •₃↺    ⟶     •₁ → •₃↺ → •₃↺
"""
l1_ = Diagram(FinDomFunctor(Dict(:A1=>arr,:A2=>ar),Dict(:a=>harr),Arr,Grph()))
l2_ = Diagram(FinDomFunctor(Dict(:X=>ar), nothing, FS, Grph()));
FS_A = FinDomFunctor(Dict(:X=>:A1), nothing, FS, Arr)
apx = Diagram(FinDomFunctor(Dict(:X=>g1), nothing, FS, Grph()))
l1 = DiagramHom(FS_A,Dict(:X=>g1arr),apx,l1_)
l2 = DiagramHom(id(FS),Dict(:X=>g1_arr1),apx,l2_)
po2 = pushout(Multispan([l1,l2]));

expected_a1 = @acset Graph begin V=3;E=3; src=[1,1,3]; tgt=[2,3,3] end
expected_a2 = @acset Graph begin V=3;E=4; src=[1,2,2,3]; tgt=[2,2,3,3] end
@test is_isomorphic(ob_map(apex(po2), Symbol("[A1,X]")), expected_a1)
@test is_isomorphic(ob_map(apex(po2), Symbol("[A2]")), expected_a2)


map([cp1, cp2, ceq, po, po2]) do clim
  @test is_functorial(diagram(apex(clim)))
  @test all(is_natural.(legs(clim)))
end

u = universal(cp1, Multicospan([F_2,CC1]))
@test is_natural(u)

# Colimits(op)
#------------
cp1 = coproduct(Diagram{op}.([LG_g1, LG_g2]));
cp2 = coproduct(Diagram{op}.([CG_g1, CG_t1ar]));
ce = coequalizer([Fop, Gop]);
po = pushout(Multispan([ALop1, ALop2]));

map([cp1, cp2, ce, po]) do clim
  @test is_functorial(diagram(apex(clim)))
  @test all(is_natural.(legs(clim)))
end

u = universal(cp1, Multicospan([ALop3, ALop2]))
@test is_natural(u)

u = factorize(ce, Qop)
@test is_natural(u)

end # module
