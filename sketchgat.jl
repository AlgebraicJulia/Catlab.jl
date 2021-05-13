using Catlab.CategoricalAlgebra.CSets
using Catlab.Present
using Catlab.Graphs
using Catlab.Theories
using Catlab.CSetDataStructures
using Combinatorics  # NON CATLAB DEPENDENCY

"""
Reference: CT for computing science: https://www.math.mcgill.ca/triples/Barr-Wells-ctcs.pdf

Here are also interesting examples + explanation of connection to Essentially Algebraic Theories: https://www.math.mcgill.ca/barr/papers/sketch.pdf

Section 7.7 describes how this is essentially the same as the
syntactic version. Maybe useful to help convert between.

FD theories add cocones and model sum types. This goes beyond what we want to model with a GAT, though may be interesting to consider for the model enumeration project, which has some initial code at the bottom.

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

Section 7.4: Arrows between FP sketches
Homomorphisms of a S sketch in category C are natural transformations btw their models (i.e. a C-Set homomorphism if C=Set)

"""


#------------------------------------------------


T = ACSetTransformation  # for brevity

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
  G::ACSet  # a Graph, arrows are "operations"
  D::Set{T} # diagrams i.e. morphisms to G
  C::Set{T} # cones i.e. morphisms to G (assume apex is V1?)
end;

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
4 <--1\\
|f  a| \\ b
v    v   v
5 <--2-->3
   e   d
"""
SquareTriangle = Graph(5)
add_edges!(SquareTriangle,[1,1,1,2,2,4],[2,3,4,3,5,5])


Square = Graph(4)
add_edges!(Square,[1,1,2,3],[2,3,4,4])

#------------------------------------------------

# Example common cones
TerminalObjCone = Graph(1)

ProductCone = Graph(3)
add_edges!(ProductCone,[1,1], [2,3]);

Product3Cone = Graph(4)
add_edges!(Product3Cone,[1,1,1],[2,3,4])

"""
     a
   1 -> 2
 b |\\c | d
   v \\ v
   3 -> 4
     e
"""
PullBackCone = Graph(4)
add_edges!(PullBackCone, [1,1,1,2,3],[2,3,4,4,4]);

#(START OF EXAMPLES)
#------------------------------------------------

# CTCS 4.6.8: SETS W/ PERMUTATIONS
SetPermGrph = Graph(1)
add_edges!(SetPermGrph,[1,1],[1,1]);  # f, g

SetPermDiagram = Graph(2)
add_edges!(SetPermDiagram, [1,2],[2,1]);

SPD = T(SetPermDiagram, SetPermGrph, V=[1,1],E=[1,2]); # f;g = g;f = id

# Model in Set must have one set and two functions to itself. Diagram forces these functions to be inverses
SetPermSketch = FLSketch(SetPermGrph, Set([SPD]), Set());

# the INITIAL term model of this is infinite when starting with a constant
# we have words like ffgggffg and can cancel out any adjacent f's and g's via the diagram

# The first 4 enumerations: empty set, singleton set+id, 2 with id, 2 with swap

#------------------------------------------------
# CTCS 4.6.9: REFLEXIVE GRAPHS

ReflG = Graph(2)
add_edges!(ReflG,[2,2,1,1], [1,1,1,2]) # src, tgt, id, refl

ReflSketch = FLSketch(ReflG, Set([
    T(Loop,     ReflG; V=[1],    E=[3]),
    T(Triangle, ReflG; V=[1,2,1],E=[4,3,1]),
    T(Triangle, ReflG; V=[1,2,1],E=[4,3,2])
    ]),Set())

#------------------------------------------------

# CTCS 7.1.5
NatNumGrph =  Graph(2) #"1", "n"
add_edges!(NatNumGrph,[1,2], [2,2])

NatNumSketch = FLSketch(NatNumGrph, Set(), Set([T(TerminalObjCone, NatNumGrph, V=[1])]));

#------------------------------------------------

# CTCS 7.1.6 INFINITE BINARY LIST

InfListG = Graph(3) # 1, d, l
add_edges!(InfListG,[1,1,3,3],[2,2,2,3])  # a, b, head, tail
InfListSketch=FLSketch(InfListG, Set(), Set([
    T(TerminalObjCone, InfListG, V=[1]),
    T(ProductCone,InfListG;V=[3,2,3],E=[3,4])]))

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

SemiGrpP2 = T(ProductCone, SemiGrpG;V=[s²,s,s],  E=[π₁, π₂])
SemiGrpP3 = T(Product3Cone,SemiGrpG;V=[s³,s,s,s],E=[Π₁,Π₂,Π₃])

SemiGrp = FLSketch(SemiGrpG, Set([SemiGrpDa, SemiGrpDb, SemiGrpDc, SemiGrpDd, SemiGrpDe]), Set([SemiGrpP2, SemiGrpP3]))


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

GraphG = Graph(2) # V, E
add_edges!(GraphG, [1,1], [2,2]) # src, tgt

DirMultiGraphSketch = FLSketch(GraphG, Set(), Set()); # directed multigraphs
#------------------------------------------------
# Example 10.1.4: SIMPLE GRAPHS

SimpleGraphG = Graph(3) # n, a, n×n
add_edges!(SimpleGraphG, [2, 2, 3, 3, 2, 2],
                         [1, 1, 1, 1, 3, 2])
                       #src,tgt,p₁,p₂,u,id

SGid = T(Loop, SimpleGraphG, V=[2], E=[6])
SGD = T(OutwardTri, SimpleGraphG, V=[2,3,1,1], E=[5,1,2,3,4])
SGcone = T(InwardTri, SimpleGraphG, V=[2,3,2,2],E=[5,6,6,5,5])
SimpleGraphSketch = FLSketch(GraphG, Set([SGid, SGD]), Set([SGcone]))


#------------------------------------------------
# 10.1.5: Categories

# note composition is defined "backwards", i.e. g∘f
CatG = Graph(4) # ob arr composable_arrows composable_triples
o,a,a²,a³ = 1:4 # shorthand
add_edges!(CatG, [o,a,a,a²,a²,a²,a³,a³,a³,a³, a³, a³, a³, a,    a,   a],
                 [a,o,o,a, a, a, a, a, a, a², a², a², a², a²,   a²,  a])
                # u s t π₁ π₂ c  p₁ p₂ p₃ p₁₂ p₂₃ p₁c cp₃ utid idus, ida
u,s,t,π₁,π₂,c,p₁,p₂,p₃,p₁₂,p₂₃,p₁c,cp₃,utid,idus,ida = 1:16
# There is a clear typo in the second diagram in CTCS
CD = Set([
    T(OutwardTri,     CatG; V=[a³,a²,a,a],    E=[p₁₂,p₁,p₂,π₁,π₂]),
    T(OutwardTri,     CatG; V=[a³,a²,a,a],    E=[p₂₃,p₂,p₃,π₁,π₂]),
    T(SquareTriangle, CatG; V=[a³,a²,a,a²,a], E=[cp₃,p₃,p₁₂,π₂,π₁,c]),
    T(SquareTriangle, CatG; V=[a³,a²,a,a²,a], E=[p₁c,p₁,p₂₃,π₁,π₂,c]),
    T(SquareTriangle, CatG; V=[a,a²,a,o,a],   E=[utid,ida,t,π₂,π₁,u]),
    T(SquareTriangle, CatG; V=[a,a²,a,o,a],   E=[idus,ida,s,π₁,π₂,u]),
    T(InvertedTri,    CatG; V=[a,a²,a,a],     E=[idus,ida,utid,ida,c]), # unit
    T(Square,         CatG; V=[a³,a²,a²,a],   E=[p₁c,cp₃,c,c]) # associativity
])

CLim1 = T(Square, CatG; V=[a²,a,a,o], E=[π₁,π₂,s,t]) # is it really a "cone"?
CLim2G = Graph(6)
add_edges!(CLim2G, [1,1,1,2,3,3,4],[2,3,4,5,5,6,6])
CLim2 = T(CLim2G, CatG; V=[a³,a,a,a,o,o], E=[p₁,p₂,p₃,s,t,s,t])

CatSketch= FLSketch(CatG, CD, Set([CLim1, CLim2]))

#------------------------------------------------
# ENUMERATING ALL MODELS PROJECT
#------------------------------------------------

# Goals:
# [ ] Find out how to compute the canonical labeling of a CSet (nauty can't do multi digraphs)
# [ ] Add impact of cones to model finding
# [ ] Debug initial term model finding algorithm
# [ ] Need a data structure for sketches *defined* as colimits
# [ ] Figure out theoretically how the models are related
# [ ] Work out a database representation of all models found
# [ ] take advantage of colimit substructure
#   - i.e. how to get the enumeration for BIG models given the enumeration of smaller models?
#   - can then solve general problem in 2 steps
#   - 1: compute required models for sub-theories
#   - 2: combine and add stuff as necessary


"""
Given all the diagrams, which paths (given by pairs of edge sequences) must commute?
"""
function comm_paths(fls::FLSketch)::Set{Pair{Vector{Int}}}
    """Find all paths in a particular diagram"""
    function cp(m::ACSetTransformation)::Set{Pair{Vector{Int}}}
        d = m.dom
        M = m.components[:E]

        # Store set of paths between each pair of vertices
        # Also store set of
        paths = Dict{Pair{Int},Set{Pair{Vector{Int},Set{Int}}}}([
            (i=>j)=>Set() for i in 1:nv(d) for j in 1:nv(d)])

        # Initialize paths with edges
        for e in 1:ne(d)
            s, t = d[:src][e], d[:tgt][e]
            push!(paths[s => t], [e] => Set([s,t])) # also keep track of 'seen' nodes
        end

        # iteratively combine paths until convergence
        changed = true
        while changed
            changed = false
            for i in 1:nv(d)
                for j in 1:nv(d)
                    fs = paths[i=>j]
                    for k in 1:nv(d)
                        gs = paths[j=>k]
                        fgs = paths[i=>k]
                        for (f, fseen) in fs
                            for (g, gseen) in gs
                                ijk = i!=j || j!= k
                                no_repeat_nodes = intersect(fseen, gseen) == Set(i==k ? [i,j] : [j])
                                if ijk && no_repeat_nodes
                                    comp = vcat(f,g) => union(fseen, gseen)
                                    # NO DUPLICATES
                                    if !(comp in fgs)
                                        changed = true
                                        push!(paths[i=>k], comp )
                                    end
                                end
                            end
                        end
                    end
                end
            end
        end
        # collect all pairs
        pairs = []
        for (ij, pths) in collect(paths)
            pths = collect(pths)  # Set -> Vector
            if ij[0] == ij[1]
                for (f,_) in pths
                    push!(pairs, f=>Int[])  # loops equal to empty path
                end
            else
                for ((f,_),(g,_)) in zip(pths,pths[2:end])  # a=b,b=c,c=d...
                    push!(pairs, f=>g)
                end
            end
        end
        return Set(map(x->M(x[1])=>M(x[2]), pairs))
    end
    return union(map(cp, collect(fls.D))...)
end

"""
General plan for enumeration:
1. Enumerate elements of ℕᵏ for an underlying graph with k nodes.
2. For each of these: (c₁, ..., cₖ), create a term model with that many constants

Do the first enumeration by incrementing n_nonzero
    and finding partitions so that ∑(c₁,...) = n_nonzero

In the future, this function will write results to a database
that hashes the FLS as well as the set of constants that generated the model.
"""
function enum(fls::FLSketch, n::Int)::Dict{Tuple,Vector{CSet}}
    res = Dict{Tuple,CSet}()
    n_const = 0 # total number of constants across all sets
    n_v = nv(fls.G)
    while length(res) < n
        n_const += 1
        for n_nonzero in 1:n_v
            # values we'll assign to nodes
            c_parts = partitions(n_const, n_nonzero)
            # Which nodes we'll assign them to
            indices = permutations(1:n_v,n_nonzero)

            for c_part in c_parts
                for index_assign in indices
                    n_const = zeros(n_v)
                    n_const[index_assign] = c_part
                    n_c = tuple(n_const...)
                    if !(n_c in res)
                        res[n_c] =  term_models(flv, n_c)
                    end
                end
            end
        end
    end

end

"""
Algorithm from Section 4.7.11 (Linear Models, pg 136) and extended by 7.6 (for FP models, pg 242).

Every FP sketch has an initial model.

Initial model has exactly one arrow (i.e. natural transformation) to every model in C. This is trivial for linear sketches b/c we map each node of the graph to ∅. However, we can add a set of constants for each node. E.g. for graphs, if we add two nodes x y and an arrow f: then the initial model is V={x,y,src(f),tgt(f)}+E={f}

We identify terms as strings of (tuples of) arrows: f;src (where f is of type 1->E). All possible such strings of tuples is the ALPHABET of the sketch.

A "Term model" requires underlying graph to not have completely disconnected objects.

The underlying theory of a sketch Th(M₀) is a CATEGORY
"Freely compose the arrows of G and impose the diagrams as equations"
Begin with the free category F(G) and construct Th(S)
and a functor Q:F(G)->Th(S) which make all diagrams D commute

NOTE: Need some heuristic for when to give up for infinite models.
Currently this infinite loops on things it shouldn't.
"""
function init_term_model(fls, consts::Tuple)::CSet
    # Initialize model
    G = fls.G
    c_paths = comm_paths(fls)

    modl = graph_to_cset(G)()
    xs = [Symbol("x$i") for i in 1:nv(G)]
    es = [Symbol("e$i") for i in 1:ne(G)]
    # Add constants
    for (i, c) in enumerate(consts)
        add_parts!(modl, xs[i], c)
    end
    # Chase constraints until convergence
    change = true
    while change
        change = false
        # loop over dangling edges
        for (i, e) in enumerate(es)
            for (j, val) in enumerate(modl[e])
                if val == 0 # && !change
                    newval = add_part!(modl, xs[G[:tgt][i]])
                    set_subpart!(modl, j, e, newval)
                    # println("x$(G[:src][i]) $j (e$i) triggered x$(G[:tgt][i]) $newval")
                    change = true
                end
            end
        end
        # loop over commuting paths
        for (p1, p2) in c_paths
            # println("checking paths $p1 $p2")
            src, tgt = G[:src][p1[1]], G[:tgt][p1[end]]
            for startval in 1:length(modl.tables[xs[src]])
                v1, v2 = startval, startval
                for e in p1
                    v1 = modl[es[e]][v1]
                end
                for e in p2
                    v2 = modl[es[e]][v2]
                end
                if v1 != v2
                    # println("merging table $tgt: $v1 $v2")
                    # Merge v1 and v2 together - 1st replace references to v2
                    for e in es[G.indices[:tgt][tgt]]
                        set_subpart!(modl, e, replace(modl[e],v2=>v1))
                    end
                    # then delete v2
                    rem_part!(modl, tbl, v2)
                    change = true
                end
            end
        end
        # change = false # uncomment to force only one iteration
    end
    return modl
end

"""
Brute force try all assignments to see if diagrams are satisfied
with the number of elements in each set fixed by consts

Algorithm:
Start of with CSet initialized to have elements for each const
(all values of FKs are "0").

For each "0" we find, branch out a possibility where it takes any possible value.
For each possibility, we first check all diagrams and fill out things we can derive
or stop if we find a contradiction. Then we again branch on the first "0" we find.
Do this until the entire CSet is defined.

To do: implement the effects of the cones
"""
function term_models(fls, consts::Tuple)::Vector{CSet}
   # Initialize model
   G = fls.G
   targets = Set(fls.G[:tgt])

   if any(x->consts[x]==0, targets)
    return [] # impossible
   end
   c_paths = comm_paths(fls)

   modl = graph_to_cset(G)()
   xs = [Symbol("x$i") for i in 1:nv(G)]
   es = [Symbol("e$i") for i in 1:ne(G)]
   # Initialize constants
   for (i, c) in enumerate(consts)
       add_parts!(modl, xs[i], c)
   end

    # For all limits:
    for cone in fls.C

    end
    # Create new limit objects from all combinations of children [FP-3]
    # (maybe do this at the start when initialize the terms)
    # Also set the projections to be correct ([FP-5])

    # NOTE: Wait until I understand finite limit diagrams before
    # implementing anything limit related -- don't want to have
    # to re-do everything from scratch

   function rec(cset::CSet)::Tuple{Vector{CSet},Set{UInt64}}
    res, seen = CSet[], Set{UInt64}([hash(cset)])

    # Fill out any info we can from diagrams, detect contradiction
    for (p1, p2) in c_paths
        # println("checking paths $p1 $p2")
        src, tgt = G[:src][p1[1]], G[:tgt][p1[end]]
        for startval in 1:length(cset.tables[xs[src]])
            v1, v2 = startval, startval
            for e in p1[1:end-1]
                if v1 != 0
                    v1 = cset[es[e]][v1]
                end
            end
            for e in p2[1:end-1]
                if v2 != 0
                    v2 = cset[es[e]][v2]
                end
            end
            nextp1 = es[p1[end]]
            if isempty(p2)
                if v1 != 0
                    next1 = cset[nextp1][v1]
                    if next1 == 0
                        set_subpart!(cset, v1, nextp1, v2)
                    elseif  next1 != v2
                        return CSet[], seen
                    end
                end
            elseif v1 != 0 || v2 != 0
                nextp1 = es[p1[end]]
                nextp2 = es[p2[end]]
                next1 = v1 == 0 ? 0 : cset[nextp1][v1]
                next2 = v2 == 0 ? 0 : cset[nextp2][v2]
                if next1 == 0 && next2 != 0
                    println("inferred that $v1 -- $nextp1 --> $next2")
                    set_subpart!(cset, v1, nextp1, next2)
                elseif v2!=0 && next2 == 0 && next1 != 0
                    println("inferred that $v2 -- $nextp2 --> $next1")
                    set_subpart!(cset, v2, nextp2, next1)
                elseif next1 != 0 && next2 != 0 && next1 != next2
                    return CSet[], seen  # violation!
                end
            end
        end
    end

    # For all limits:
    # When setting two limit objects equal, need to equate their children

    # split cases on an arbitrary choice for the first zero we find
    for (i, e) in enumerate(es)
        tgt_table = xs[G[:tgt][i]]
        for (j, val) in enumerate(cset[e])
            if val == 0  #SPLIT
                for k in 1:length(cset.tables[tgt_table])
                    cset2 = deepcopy(cset)
                    set_subpart!(cset2, j, e, k)
                    if !(hash(cset2) in seen)
                        newres, newseen = rec(cset2)
                        append!(res, newres)
                        union!(seen, newseen)
                    end
                end
                return res, seen
            end
        end
    end
    return [cset], seen
   end

   return rec(modl)[1]
end

"""
Create a CSet type specified by a graph
Vertices are x₁,x₂,..., edges are e₁, e₂,...
"""
function graph_to_cset(grph::CSet)::Type
    pres = Presentation(FreeSchema)
    xs = [Ob(FreeSchema,Symbol("x$i")) for i in 1:nv(grph)]
    for x in xs
        add_generator!(pres, x)
    end
    for (i,(src, tgt)) in enumerate(zip(grph[:src], grph[:tgt]))
        add_generator!(pres, Hom(Symbol("e$i"), xs[src], xs[tgt]))
    end
    return CSetType(pres)
end

#------------------------------------------------
# Tests
#------------------------------------------------
bool_perms = term_models(SetPermSketch,(2,)) # id and swap
