using Catlab.CategoricalAlgebra.CSets
using Catlab.Present
using Catlab.Graphs
using Catlab.Theories
using Catlab.CSetDataStructures
using Combinatorics  # NON CATLAB DEPENDENCY
using Catlab.WiringDiagrams
using Catlab.Programs
import Random: shuffle
import DataStructures: IntDisjointSets, in_same_set
import Base: size, hash

"""
Reference: CT for computing science: https://www.math.mcgill.ca/triples/Barr-Wells-ctcs.pdf

We are concerned with "Regular" sketches, where no node is the vertex of more than one cone.

Here are also interesting examples + explanation of connection to Essentially Algebraic Theories: https://www.math.mcgill.ca/barr/papers/sketch.pdf

Section 7.7 describes how this is essentially the same as the
syntactic version. Maybe useful to help convert between.

FD theories add cocones and model sum types. This goes beyond what we want to model with a GAT, though may be interesting to consider for the model enumeration project, which has some code at the bottom.

Also check Fiore: categorical semantics of dependent type theory
"""

"""
Section 7.3+10.1.3 Shorthand Caveats:
2. nodes a×b×c IMPLICITLY have a cone with projection legs.
3. likewise nodes labeled 1 are implicitly terminal (empty base limit)
4. arrows labeled ⟨f₁,f₂,...⟩:a->b₁×b₂×... , where edges fₙ all share a codomain, are implicitly assumed to have diagrams:
                fᵢ
              a ⟶ bᵢ
 ⟨f₁,f₂,...⟩  ↓   ↗ pᵢ
          b₁×b₂×...

5. arrows labeled f₁×f₂×...: a₁×a₂×...->b₁×b₂×...
are implicitly assumed to have diagrams:
                 pᵢ
      a₁×a₂×... --> aᵢ
f₁×f₂×...↓          ↓ fᵢ
      b₁×b₂×... --> bᵢ
                pᵢ

6. diagrams of the form of two paths with a common start and end can be specified as s₁;s₂;... = t₁;t₂;...
7. If one leg of the above paths is empty, we require an identity arrow and set the other path to be equal to it.
8. Nodes labeled a×ᵧb implies the existence of a cone
        a×ᵧb
       ↙   ↘
      a→ γ ←b
9. an arrow s: a↣b (i.e. s is monic) implies the existence of a cone
        a
   id ╱ | ╲ id
    ↙   ↓s  ↘
   a ⟶ b ⟵ a
     s     s
"""

"""
Section 7.4: Arrows between FP sketches
Homomorphisms of a S sketch in category C are natural transformations btw their models (i.e. a C-Set homomorphism if C=Set)
"""


#------------------------------------------------


T = CSetTransformation  # for brevity

#------------------------------------------------

"""
Data for a finite limit sketch: graph G + diagrams/cones that map into G
"""
@present TheoryFLSketch(FreeSchema) begin
    (V, E)::Ob
    (src, tgt)::Hom(E,V)

    (Cone, Cv, Ce)::Ob
    (cSrc, cTgt)::Hom(Ce,Cv)
    cV::Hom(Cv, Cone)
    cE::Hom(Ce, Cone)
    apex::Hom(Cone, Cv)

    (Diagram, Dv, De)::Ob
    (dSrc, dTgt)::Hom(De,Dv)
    dV::Hom(Dv, Diagram)
    dE::Hom(De, Diagram)

    # Homorphisms data
    cvMap::Hom(Cv, V)
    ceMap::Hom(Ce, E)
    dvMap::Hom(Dv, V)
    deMap::Hom(De, E)

    # Diagrams/cones don't touch each other
    compose(apex, cV) == id(Cone)
    compose(cSrc, cV) == cE
    compose(cTgt, cV) == cE
    compose(dSrc, dV) == dE
    compose(dTgt, dV) == dE

    # Homomorphism properties
    compose(deMap, src) == compose(dSrc, dvMap)
    compose(deMap, tgt) == compose(dTgt, dvMap)
    compose(ceMap, src) == compose(cSrc, cvMap)
    compose(ceMap, tgt) == compose(cTgt, cvMap)
end;

#------------------------------------------------

"""
Tradeoffs vs a julia data structure? (acsets presumed to be graphs)
"""
struct FLSketch
  G::CSet  # a Graph, arrows are "operations"
  D::Vector{T} # diagrams i.e. morphisms to G
  C::Vector{Pair{Int,T}} # apex + edges in G from apex
  function FLSketch(G::CSet,D::Vector{T},C::Vector{Pair{Int,T}})
    for t in D
      @assert is_natural(t)
    end
    for (_, t) in C
      @assert is_natural(t)
    end
    return new(G,D,C)
  end
end

function FLSketch(G::CSet)
  return FLSketch(G,Vector{T}(), Vector{Pair{Int,T}}())
end
function FLSketch(G::CSet, D::Vector{T})
  return FLSketch(G,D, Vector{Pair{Int,T}}())
end
function FLSketch(G::CSet, C::Vector{Pair{Int,T}})
  return FLSketch(G, Vector{T}(), C)
end

"""
The domain of a cone morphism
with the cone and its legs removed
"""
function remove_cone(dia::CSet, apex::Int)::CSet
  res = Graph(nv(dia)-1)
  offset = [i>apex ? i-1 : i for i in 1:nv(dia)]
  for (src, tgt) in zip(dia[:src], dia[:tgt])
    @assert tgt != apex
    if src != apex
      add_edge!(res, offset[src], offset[tgt])
    end
  end
  return res
end

"""
Given a cone diagram, what do vertices in the base
correspond to tables in G? What do edges from the
apex correspond to (if any)?
"""
function cone_dia_map(m::T,apex::Int)::Tuple{Vector{Int},Vector{Int}, Vector{Int}}
  G = dom(m)
  tgttab = [m[:V](i) for i in 1:nv(G) if i!=apex]
  out = Dict([G[:tgt][leg]=>m[:E](leg)
              for leg in G.indices[:src][apex]])
  legs = [get(out,i,0) for i in 1:nv(G) if i!=apex]
  dia_emap = [m[:E](e)  for e in 1:ne(G) if G[:src][e]!=apex]
  return tgttab, dia_emap, legs
end

# not all legs from apex need to be defined. Because a valid cone has
# only ONE arrow to each object in the diagram, it's redundant to
# specify an arrow from A to C if the diagram already has B->C.
# For these nodes, an edge value of 0 can be used as a null value.
#------------------------------------------------

# Example common diagrams
Triangle = Graph(3) # f;g=h
add_edges!(Triangle, [1,1,2], [2,3,3]) # f,h,g

Loop = Graph(1)
add_edge!(Loop, 1, 1)

"""
      1
  b↙ a↓  ↘ c
 3 ⟵ 2 ⟶ 4
   d   e
"""
OutwardTri = Graph(4)
add_edges!(OutwardTri, [1,1,1,2,2], [2,3,4,3,4])

"""
      4
  b↗ e↑  ↖ d
 1 ⟶ 2 ⟵ 3
   a     c
"""
InvertedTri = Graph(4)
add_edges!(InvertedTri, [1,1,3,3,2],[2,4,2,4,4])

"""
      1
  b↙ a↓  ↘ c
 3 ⟶ 2 ⟵ 4
   d   e
"""
InwardTri = Graph(4)
add_edges!(InwardTri, [1,1,1,3,4], [2,3,4,2,2])


"""
     c
  4<--1
f ↓  a↓ ↘ b
  5<--2-->3
    e   d
"""
SquareTriangle = Graph(5)
add_edges!(SquareTriangle,[1,1,1,2,2,4],[2,3,4,3,5,5])


Square = Graph(4)
add_edges!(Square,[1,1,2,3],[2,3,4,4])

#------------------------------------------------

# Example cones

"""
   * ⟶ 2
   ↓ ↘  ↓ b
   1 ⟶ 3
     a
"""
Cospan = Graph(3) # cospan
add_edges!(Cospan, [1,2],[3,3]);
Span = Graph(3) # span
add_edges!(Span, [1,1],[2,3]);
Span3 = Graph(4) # span
add_edges!(Span3, [1,1,1],[2,3,4]);

#(START OF EXAMPLES)
#------------------------------------------------

# CTCS 4.6.8: SETS W/ PERMUTATIONS
SetPermGrph = Graph(1)
add_edges!(SetPermGrph,[1,1],[1,1]);  # f, g

SetPermDiagram = Graph(2)
add_edges!(SetPermDiagram, [1,2],[2,1]);

SPD = T(SetPermDiagram, SetPermGrph, V=[1,1],E=[1,2]); # f;g = g;f = id

# Model in Set must have one set and two functions to itself. Diagram forces these functions to be inverses
SetPermSketch = FLSketch(SetPermGrph, T[SPD]);

# the INITIAL term model of this is infinite when starting with a constant
# we have words like ffgggffg and can cancel out any adjacent f's and g's via the diagram

# The first 4 enumerations: empty set, singleton set+id, 2 with id, 2 with swap

#------------------------------------------------
# CTCS 4.6.9: REFLEXIVE GRAPHS

ReflG = Graph(2)
add_edges!(ReflG,[2,2,1,1], [1,1,1,2]) # src, tgt, id, refl

ReflSketch = FLSketch(ReflG, T[
    T(Loop,     ReflG; V=[1],    E=[3]),
    T(Triangle, ReflG; V=[1,2,1],E=[4,3,1]),
    T(Triangle, ReflG; V=[1,2,1],E=[4,3,2])])

#------------------------------------------------

# CTCS 7.1.5
NatNumGrph =  Graph(2) #"1", "n"
add_edges!(NatNumGrph,[1,2], [2,2])

NatNumSketch = FLSketch(NatNumGrph, Pair{Int,T}[
  1=>T(Graph(1), NatNumGrph, V=[1])]);

#------------------------------------------------

# CTCS 7.1.6 INFINITE BINARY LIST

InfListG = Graph(3) # 1, d, l
add_edges!(InfListG,[1,1,3,3],[2,2,2,3])  # a, b, head, tail
InfListSketch=FLSketch(InfListG, Pair{Int,T}[
  1=>T(Graph(1), InfListG, V=[1]),
  1=>T(Span,InfListG;V=[3,2,3],E=[3,4])])

# We CANNOT make a finite model out of this

#------------------------------------------------

# CTCS 7.2: Semigroup
SemiGrpG = Graph(3) # s s² s³
add_edges!(SemiGrpG, [2, 2, 2, 2, 2, 2,   3,   3,    3,   3],
                     [1, 1, 1, 1, 1, 1,   2,   2,    2,   2]);
#                     π₁ k  π₂ Π₁ Π₂ Π₃ π₁×π₂ π₂×π₃ id×k k×id
s,s²,s³ = 1:3
π₁,k,π₂,Π₁,Π₂,Π₃,π₁π₂,π₂π₃,idk,kid = 1:10
# A,B are needed to define arrows that appear in C,D
SemiGrpDa = T(OutwardTri,SemiGrpG;V=[s³,s²,s,s],E=[π₁π₂,π₁,π₂,Π₁,Π₂])
SemiGrpDb = T(OutwardTri,SemiGrpG;V=[s³,s²,s,s],E=[π₂π₃,π₁,π₂,Π₂,Π₃])
# C,D are needed to define arrows that appear in E
SemiGrpDc = T(SquareTriangle,SemiGrpG;V=[s³,s²,s,s²,s],E=[kid, Π₃,π₁π₂,π₂,π₁,k])
SemiGrpDd = T(SquareTriangle,SemiGrpG;V=[s³,s²,s,s²,s],E=[idk, Π₁,π₂π₃,π₁,π₂,k])
# E: associativity constraint
SemiGrpDe = T(Square,SemiGrpG;V=[s³,s²,s²,s],E=[idk,kid,k,k])

SemiGrpP2 = T(Span, SemiGrpG;V=[s²,s,s],  E=[π₁, π₂])
SemiGrpP3 = T(Span3,SemiGrpG;V=[s³,s,s,s],E=[Π₁,Π₂,Π₃])

# IS NATURAL VIOLATION
# SemiGrp = FLSketch(SemiGrpG, T[
#     SemiGrpDa, SemiGrpDb, SemiGrpDc, SemiGrpDd, SemiGrpDe],
#     Pair{Int,T}[1=>SemiGrpP2, 1 => SemiGrpP3])


#------------------------------------------------

#------------------------------------------------

# Sketch of theory of groups
# G vertices:  with id arrows
# m: G²->G, i:G->G, u:1->G
# 5 projection arrows for cones: pᵢ:G²->G, qᵢ:G³->G
# Arrow G->1
# rᵢ: G->G² (which will be forced to be id×u and u×id)
# sᵢ: G->G² (will be (id,i) and (i,id)) ???
# tᵢ: G³->G² (will be (q₁,q₂) and (q₂, q₃))
# nᵢ: G³->G² (will be id×m and m×id)

# Diagrams
#      /-G  --> 1
#  id/   |r₁    | u
#  v    v       v
# G <-- G² --> G

GroupG = Graph(4)  # 1, G, G², G³
add_edges!(GroupG, [3,2,1,3,3,4,4,4,2,2,2,2,2,4,4,4,4],
                   [2,2,2,2,2,3,3,3,1,3,3,3,3,3,3,3,3])
                  # m,i,u,p₁p₂q₁q₂q₃!,r₁r₂s₁s₂t₁t₂n₁n₂

# TODO diagrams/limits

#------------------------------------------------
# 10.4.3: Monomorphisms
MonoG = Graph(2) # a b
add_edges!(MonoG, [1,1], [1,2]) # id, f

MonoCone = T(InwardTri, MonoG,V=[1,2,1,1],E=[2,1,1,2,2])
MonoSketch=FLSketch(MonoG,
    T[T(Loop,MonoG,V=[1], E=[1])], # force ID arrow
    Pair{Int,T}[1=>MonoCone])
#------------------------------------------------
ProdSketch= FLSketch(Span, Pair{Int,T}[1=> id(Span)])
#------------------------------------------------

GraphG = Graph(2) # V, E
add_edges!(GraphG, [1,1], [2,2]) # src, tgt

DirMultiGraphSketch = FLSketch(GraphG); # directed multigraphs
#------------------------------------------------
# Example 10.1.4: SIMPLE GRAPHS

SimpleGraphG = Graph(3) # n, a, n×n
add_edges!(SimpleGraphG, [2, 2, 3, 3, 2, 2],
                         [1, 1, 1, 1, 3, 2])
                       #src,tgt,p₁,p₂,u,id

SGid = T(Loop, SimpleGraphG, V=[2], E=[6]);
src_tgt_equal = T(OutwardTri, SimpleGraphG, V=[2,3,1,1], E=[5,1,2,3,4]);

SGcone = T(InwardTri, SimpleGraphG, V=[2,3,2,2],E=[5,6,6,5,5])
u_monic = T(InwardTri, SimpleGraphG, V=[2,2,2,3],E=[6,5,6,6,5]);
# NATURAL FAIL
# SimpleGraphSketch = FLSketch(SimpleGraphG,
#     T[SGid, src_tgt_equal],
#     Pair{Int,T}[1=>SGcone, 1=>u_monic]);


#------------------------------------------------
# 10.1.5: Categories

# note composition is defined "backwards", i.e. g∘f
CatG = Graph(4) # ob arr composable_arrows composable_triples
o,a,a²,a³ = 1:4 # shorthand
add_edges!(CatG, [o,a,a,a²,a²,a²,a³,a³,a³,a³, a³, a³, a³, a,    a,   a],
                 [a,o,o,a, a, a, a, a, a, a², a², a², a², a²,   a²,  a])
                # u s t π₁ π₂ c  p₁ p₂ p₃ p₁₂ p₂₃ p₁c cp₃ utid idus, ida
u,s,t,π₁,π₂,c,p₁,p₂,p₃,p₁₂,p₂₃,p₁c,cp₃,utid,idus,ida,v = 1:17
# There's a clear typo in the second diagram in CTCS
CD = T[
    T(OutwardTri,     CatG; V=[a³,a²,a,a],    E=[p₁₂,p₁,p₂,π₁,π₂]),
    T(OutwardTri,     CatG; V=[a³,a²,a,a],    E=[p₂₃,p₂,p₃,π₁,π₂]),
    T(SquareTriangle, CatG; V=[a³,a²,a,a²,a], E=[cp₃,p₃,p₁₂,π₂,π₁,c]),
    T(SquareTriangle, CatG; V=[a³,a²,a,a²,a], E=[p₁c,p₁,p₂₃,π₁,π₂,c]),
    T(SquareTriangle, CatG; V=[a,a²,a,o,a],   E=[utid,ida,t,π₂,π₁,u]),
    T(SquareTriangle, CatG; V=[a,a²,a,o,a],   E=[idus,ida,s,π₁,π₂,u]),
    T(InvertedTri,    CatG; V=[a,a²,a,a],     E=[idus,ida,utid,ida,c]), # unit
    T(Square,         CatG; V=[a³,a²,a²,a],   E=[p₁c,cp₃,c,c]) # associativity
]

CLim1 = T(Square, CatG; V=[a²,a,a,o], E=[π₁,π₂,s,t]) # is it really a "cone"?
CLim2G = Graph(6)
add_edges!(CLim2G, [1,1,1,2,3,3,4],[2,3,4,5,5,6,6])
CLim2 = T(CLim2G, CatG; V=[a³,a,a,a,o,o], E=[p₁,p₂,p₃,s,t,s,t])

CatSketch= FLSketch(CatG, CD, Pair{Int,T}[1 => CLim1, 1 => CLim2])




