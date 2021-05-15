using Catlab.CategoricalAlgebra.CSets
using Catlab.Present
using Catlab.Graphs
using Catlab.Theories
using Catlab.CSetDataStructures
using Combinatorics  # NON CATLAB DEPENDENCY
using Catlab.WiringDiagrams
using Catlab.Programs
import Random: shuffle

"""
Reference: CT for computing science: https://www.math.mcgill.ca/triples/Barr-Wells-ctcs.pdf

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
  C::Set{Tuple{T,Int,Vector{Int}}} # apex + edges in G from apex
end;
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

NatNumSketch = FLSketch(NatNumGrph, Set(), Set([
    (T(Graph(0), NatNumGrph), 1, [])]));

#------------------------------------------------

# CTCS 7.1.6 INFINITE BINARY LIST

InfListG = Graph(3) # 1, d, l
add_edges!(InfListG,[1,1,3,3],[2,2,2,3])  # a, b, head, tail
InfListSketch=FLSketch(InfListG, Set(), Set([
    (T(Graph(0), InfListG), 1,[]),
    (T(Graph(2),InfListG;V=[2,3]), 3, [3,4])]))

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

SemiGrpP2 = (T(Graph(2), SemiGrpG;V=[s,s]), s²,[π₁, π₂])
SemiGrpP3 = (T(Graph(3),SemiGrpG;V=[s,s,s]),s³,[Π₁,Π₂,Π₃])

SemiGrp = FLSketch(SemiGrpG, Set([
    SemiGrpDa, SemiGrpDb, SemiGrpDc, SemiGrpDd, SemiGrpDe]),
    Set([SemiGrpP2, SemiGrpP3]))


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
MonoG = Graph(2)
add_edges!(MonoG, [1,1], [1,2])

MonoCone = T(Cospan, MonoG,V=[1,1,2],E=[2,2])
MonoSketch=FLSketch(MonoG,
    Set([T(Loop,MonoG,V=[1], E=[1])]), # force ID arrow
    Set([(MonoCone,1,[1,1])]))
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

SGid = T(Loop, SimpleGraphG, V=[2], E=[6]);
src_tgt_equal = T(OutwardTri, SimpleGraphG, V=[2,3,1,1], E=[5,1,2,3,4]);

nn_prod = (T(Graph(2), SimpleGraphG, V=[1,1]), 3, [3,4]);


u_monic = (T(Cospan, SimpleGraphG, V=[2,2,3],E=[5,5]), 2, [6,6,5]);
SimpleGraphSketch = FLSketch(SimpleGraphG,
    Set([SGid, src_tgt_equal]),
    Set([nn_prod, u_monic]));


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

CLim1 = (T(Cospan, CatG; V=[a,a,o], E=[s,t]), a², [π₁,π₂,0])
CLim2G = Graph(5)
add_edges!(CLim2G, [1,2,2,3],[4,4,5,5])
CLim2 = (T(CLim2G, CatG; V=[a,a,a,o,o], E=[s,t,s,t]), a³, [p₁,p₂,p₃,0,0])

CatSketch= FLSketch(CatG, CD, Set([CLim1, CLim2]))


#------------------------------------------------
# ENUMERATING ALL MODELS PROJECT
#------------------------------------------------

# Goals:
# [x] Find out how to compute the canonical labeling of a CSet (nauty can't do multi digraphs)
# [x] Add impact of cones to model finding
# [ ] Need a data structure for sketches *defined* as colimits
# [ ] Figure out theoretically how the models are related
# [ ] Work out a database representation of all models found
# [ ] take advantage of colimit substructure
#   - i.e. how to get the enumeration for BIG models given the enumeration of smaller models?
#   - can then solve general problem in 2 steps
#   - 1: compute required models for sub-theories
#   - 2: combine and add stuff as necessary
# [ ] Less important: debug initial term model finding algorithm


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
            if ij[1] == ij[2]
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
Brute force try all assignments to see if diagrams are satisfied
with the number of elements in each set fixed by consts

Algorithm:
- Start of with CSet initialized to have elements for each const
  plus one extra value meant to represent unknown (call it u).
- All values of FKs are initialized to u.
- For each u we find, branch out a possibility where it takes any possible value.

- For each possibility, check all diagrams
  - positive info: fill out things we can derive if one leg is known and other unknown
  - negative info: find a contradiction, short circuit
- For each cone, check its base diagram and for each matching set of elements
  - positive info: TBD, I think there is a lot we can infer, however
  - negative info: if nothing could be an apex or two different things are an apex, fail

- Repeat this until the entire CSet is defined, then trim off the 'unknown' values.

Current problem: evaluating a query on a discrete cone fails for catlab reasons
"""
function term_models(fls, consts::Tuple)::Vector{CSet}

    # Initialize model
    G = fls.G
    modl = graph_to_cset(G)()
    xs = [Symbol("x$i") for i in 1:nv(G)]
    es = [Symbol("e$i") for i in 1:ne(G)]

    # Initialize constants + EXTRA SENTINAL VALUE = "UNKNOWN"
    for (i, c) in enumerate(consts)
        add_parts!(modl, xs[i], c+1;)
    end
    # initialize foreign keys to unknown value
    for e in 1:ne(G)
        n_in, n_out = [nparts(modl, G[x][e]) for x in [:src, :tgt]]
        set_subparts!(modl, 1:n_in; Dict([es[e]=>n_out])...)
    end

    # Initialize commutative diagram data
    c_paths = comm_paths(fls)
    comm_qs = [paths_to_query(G, p1, p2) for (p1, p2) in c_paths]
    comm_q_tabs = [xs[lasttabs(G, p1, p2)] for (p1, p2) in c_paths]

    # Initialize cone data
    cone_ds = [diagram_to_query(cone[1]) for cone in fls.C]
    cone_tabs = [xs[cone[1].components[:V].func] for cone in fls.C]

    function rec!(cset::CSet, res::Vector{CSet},seen::Set{UInt64})
        # Fill out any info we can from diagrams, detect contradiction
        for (comm_q, cqtab, (pth1, pth2)) in zip(comm_qs, comm_q_tabs, c_paths)
            for qres in query(cset, comm_q)
                penult1, penult2, last1, last2 = qres
                nullp1, nullp2, null1, null2 = map(
                    tabval -> tabval[2] == nparts(cset, tabval[1]), zip(cqtab, qres))
                if null1 && !null2 && !nullp1 # can propagate info
                    set_subpart!(cset, penult1, es[pth1[end]], last2)
                elseif !null1 && null2 && !nullp2 # can propagate info
                    set_subpart!(cset, penult2, es[pth2[end]], last1)
                elseif !(null1||null2)  # can check for contradiction
                    if last1 != last2
                        return
                    end
                end
            end
        end

        for (dia, c_tabs, (_, apex, legs)) in zip(cone_ds, cone_tabs, fls.C)
            npart = nparts(cset, apex)
            for matches in query(cset, dia)
                if all(i->matches[i] < nparts(cset,c_tabs[i]), 1:length(c_tabs)) # ignore matches with unknowns
                    poss_apexes = Set(1:npart)
                    for (legval,leg) in zip(matches,legs)
                        if leg != 0
                            leg_edge = es[leg]
                            intersect!(poss_apexes, cset.indices[leg_edge][legval])
                        end
                    end
                    has_null, n_apex = npart in poss_apexes, length(poss_apexes)
                    if  !(n_apex in (has_null ? [1,2] : [1]))
                        return
                    end
                end
            end
        end

        # split cases on an arbitrary choice for the first zero we find
        for (i, e) in shuffle(collect(enumerate(es)))
            tgt_table = xs[G[:tgt][i]]
            for (j, val) in shuffle(collect(enumerate(cset[e][1:end-1])))
                if val == nparts(cset, tgt_table)  #SPLIT
                    for k in 1:(val-1)
                        cset2 = deepcopy(cset)
                        set_subpart!(cset2, j, e, k)
                        hsh = canonical_hash(cset2)
                        if !(hsh in seen)
                            push!(seen,hsh)
                            rec!(cset2, res, seen)
                        end
                    end
                    return res
                end
            end
        end
        # No unknown values! Delete the last value from every table
        for t in keys(cset.tables)
            rem_part!(cset, t, nparts(cset, t))
        end
        hsh = canonical_hash(cset)
        if hsh in seen
            return
        else
            push!(seen, hsh)
            push!(res, cset)
        end
    end
    res, seen = CSet[], Set{UInt64}()
    rec!(modl, res, seen)
    return res
end

"""
Create a CSet type specified by a graph
Vertices are x₁,x₂,..., edges are e₁, e₂,...
"""
function graph_to_cset(grph::CSet)::Type
    pres = Presentation(FreeSchema)
    xs = [Ob(FreeSchema,Symbol("x$i")) for i in 1:nv(grph)]
    es = [Symbol("e$i") for i in 1:ne(grph)]
    for x in xs
        add_generator!(pres, x)
    end
    for (i,(src, tgt)) in enumerate(zip(grph[:src], grph[:tgt]))
        add_generator!(pres, Hom(es[i], xs[src], xs[tgt]))
    end
    return CSetType(pres, index=es)
end

"""
Take in a Graph CSet, return wiring diagram Cset that
queries a CSet with the schema generated by `graph_to_cset` above

Actually use morphism which renames objects and edges, in case
d is a pattern to be interpreted in the context of another graph
"""
function diagram_to_query(m::ACSetTransformation)
    d  = m.dom
    xs = [Symbol("x$(m.components[:V](i))") for i in 1:nv(d)]
    xnames = [Symbol("$(x)_$i") for (i, x) in enumerate(xs)]
    es = [Symbol("e$(m.components[:E](i))") for i in 1:ne(d)]
    rel = RelationDiagram{Symbol}(nv(d),port_names=xnames) # port_names=xs
    add_junctions!(rel, nv(d),variable=xnames)
    set_subpart!(rel, 1:nv(d), :outer_junction, 1:nv(d))
    for v in 1:nv(d)
        outarrows = d.indices[:src][v]
        b = add_box!(rel, 1+length(outarrows), name=xs[v])
        ps = ports(rel, b)
        set_subpart!(rel, ps, :port_name, vcat([:_id],es[outarrows]))
        set_junction!(rel, ps, vcat([v],d[:tgt][outarrows]))
    end
    return rel
end

"""
Given two paths, [a₁,a₂,...] and [b₁, b₂,...] we want a query that
returns the penultimate and final nodes values along both paths
for each element in the source table, src(a₁)=src(b₁).
"""
function paths_to_query(d::ACSet, p1::Vector{Int}, p2::Vector{Int})
    n1, n2 = map(length, [p1, p2])
    xs = [Symbol("x$i") for i in 1:nv(d)]
    es = [Symbol("e$i") for i in 1:ne(d)]
    res = [Symbol("$s$i") for s in ["pen", "last"] for i in 1:2]
    rel = RelationDiagram{Symbol}(4,port_names=res)
    root = add_box!(rel, n2 > 0 ? 3 : 2, name=xs[d[:src][p1[1]]])
    ps = ports(rel, root)
    add_junctions!(rel, 1, variable=[:init])
    set_junction!(rel, [ps[1]], [1])
    set_subpart!(rel, ps[1], :port_name, :_id)

    for (p_index,path) in [1=>p1, 2=>p2]
        if isempty(path)

        else
            outport = ps[p_index+1]
            lastj, = add_junctions!(rel, 1, variable=[Symbol("p_$(p_index)_1")])
            set_junction!(rel, [outport], [lastj])
            for (i, arr) in enumerate(path)
                set_subpart!(rel, outport, :port_name, es[arr])
                if i < length(path)
                    j, = add_junctions!(rel, 1, variable=[Symbol("p_$(p_index)_$(i+1)")])
                    b = add_box!(rel, 2, name=xs[d[:tgt][arr]])
                    pid, pout = ports(rel, b)
                    set_subpart!(rel, pid, :port_name, :_id)
                    set_junction!(rel, [pid,pout], [lastj, j])
                    outport = pout
                    lastj = j
                end
            end
        end
    end
    set_subpart!(rel, 1:4, :outer_junction, [
        n1, n2 < 2 ? 1 : n1+n2, n1+1, n2 == 0 ? 1 : n1+n2+1])
    return rel
end

"""
Helper function to get the penultimate and
last tables of a pair of commutative paths
(note we only allow p2 to be empty)
"""
function lasttabs(d::ACSet, p1::Vector{Int}, p2::Vector{Int})::Vector{Int}
    root =d[:src][p1[1]]
    penult_1, last_1 = [d[x][p1[end]] for x in [:src, :tgt]]
    penult_2 = isempty(p2) ? root : d[:src][p2[end]]
    last_2 = isempty(p2) ? root : d[:tgt][p2[end]]
    return [penult_1, penult_2, last_1, last_2]
end

#------------------------------------------------
# automorphisms
#------------------------------------------------

CDict = Dict{Symbol, Vector{Int}}

"""Compute all automorphisms of a CSet"""
function autos(g::CSet) :: Set{CDict}
    res = Set{CDict}()
    seen = Set{CDict}()
    comps = keys(g.tables)
    cs = Dict([comp=>ones(Int, length(t)) for (comp, t)
                in zip(comps, g.tables)])
    for comp in comps
        for i in 1:length(cs[comp])
            new_cs = deepcopy(cs)
            new_cs[comp][i] = 2
            branch!(g, new_cs, res, seen)
        end
    end
    return res
end

"""Take a random color with multiple nodes and split"""
function branch!(g::CSet, cs::CDict, res::Set{CDict}, seen::Set{CDict})
    comps = collect(keys(g.tables))

    for comp in shuffle(comps)
        if length(cs[comp]) != length(Set(cs[comp]))
            seen_colors = Set()
            for (i, c) in enumerate(cs[comp])
                if c in seen_colors
                    updated_cs = update_colors(g, deepcopy(cs), comp, i)
                    if !(updated_cs in seen)
                        push!(seen, updated_cs)
                        branch!(g, updated_cs, res, seen)
                    end
                else
                    push!(seen_colors, c)
                end
            end

            return
        end
    end
    push!(res, cs)
end
"""Differentiate elements by how many nodes of each color they touch"""
function update_colors(g::CSet, cs::CDict, tbl::Symbol, val::Int)::CDict
    comps, arr, src, tgt = typeof(g).parameters[1].parameters

    incident = Dict([comp=>([(a,comps[s]) for (a,s,t) in zip(arr,src,tgt)
                     if t == i]) for (i, comp) in enumerate(comps)])

    new_color = maximum(cs[tbl]) + 1
    cs[tbl][val] = new_color

    # propagate info for everything incident to tbl
    for (arrow, srctab) in incident[tbl]
        # partition source table by # of each color that is touched through arrow
        counts = [zeros(Int, new_color) for _ in  1:length(g.tables[srctab])]
        for (color, preimage) in zip(cs[tbl], g.indices[arrow])
            for elem in preimage
                counts[elem][color] += 1
            end
        end
        hshs = map(hash, counts)
        parts = Dict([h=>[] for h in hshs])
        for (i,h) in enumerate(hshs)
            push!(parts[h],i)
        end
        old_max = maximum(cs[srctab])
        orig_parts = [[i for (i,col) in enumerate(cs[srctab])
                      if col==c] for c in 1:old_max]
        # change colors if needed
        for part in filter(x->length(x)>1, orig_parts)
            parthsh = [hshs[i] for i in part]
            hshdict = Dict([h=>[] for h in collect(Set(parthsh))])
            for (h, i) in zip(parthsh, part)
                push!(hshdict[h],i)
            end
            for (offset, is) in enumerate(collect(values(hshdict))[2:end]) # first partition keeps label
                cs[srctab][is] .= old_max + offset
            end
        end
    end
    return cs
end
"""Apply a coloring to a Cset to get an isomorphic cset"""
function apply_automorphism(c::CSet,d::CDict)::CSet
    new = deepcopy(c)
    tabs, arrs, _, tgts = (typeof(c).parameters[1]).parameters
    for (arr, tgti) in zip(arrs,tgts)
        tgt = tabs[tgti]
        set_subpart!(new, arr, d[tgt][c[arr]])
    end
    return new
end
function canonical_iso(g::CSet)::CSet
    isos = sort([apply_automorphism(g, Dict(a)) for a in autos(g)], by=string)
    return isos[1]
end
function canonical_hash(g::CSet)::UInt64
    return hash(string(canonical_iso(g)))
end
#------------------------------------------------
# Tests
#------------------------------------------------
q1 = diagram_to_query(nn_prod[1])
q2 = diagram_to_query(u_monic[1])
xg = graph_to_cset(SimpleGraphG)()
for i in 1:3 add_parts!(xg, Symbol("x$i"), 3) end
for i in 1:6 set_subpart!(xg, Symbol("e$i"), [3,3,3]) end
q3 = @relation (x1=x1_1) begin
    x1(_id=x1_1)
end

# indexing schema: e1::x2 → x1
q32 = @relation (x1=x1_1,x2=x2_1) begin
x1(_id=x1_1)
x2(_id=x2_1,e1=x1_1) # need e1 or it fails
end

sg_res = term_models(SimpleGraphSketch, (2,2,2))# n, a, n×n

if 1+1==0 # don't run these automatically

bool_perms = term_models(SetPermSketch,(2,)) # finds id and swap
mono_res = term_models(MonoSketch, (2,2)) # finds the two isomorphic swap functions


# TEST DIAGRAM TO QUERY

rg = @relation (V1=v1,V2=v2) begin
 E(src=v1, tgt=v2)
 V(_id=v1)
end

r = diagram_to_query(id(Triangle))

rel = @relation (x1=x1,x2=x2,x3=x3) begin
 x1(_id=x1, e1=x2, e2=x3)
 x2(_id=x2,e3=x3)
 x3(_id=x3)
end

@assert is_isomorphic(r, rel)

tri = graph_to_cset(Triangle)()
for i in 1:3 add_parts!(tri, Symbol("x$i"), 2) end
for i in 1:3 set_subpart!(tri, Symbol("e$i"), [1,2]) end
res = query(tri, rel)
for i in 1:2
    @assert res[i] == (x1=i,x2=i,x3=i)
end

# TEST PATHS TO QUERY
xgraph = Graph(4) # two paths that meet up but intersect along the way
add_edges!(xgraph, [1,2,1,2,4],[2,3,2,4,3])
xg = graph_to_cset(xgraph)()
for i in 1:4 add_parts!(xg, Symbol("x$i"), 2) end
for (i, p) in enumerate([[1,2],[2,1],[2,1],[2,1],[2,2]])
    set_subpart!(xg, Symbol("e$i"),p)
end

p1 = [1,2]  # (12)→(12)→(21)  # pen1 = 1;2, last1 = 2;1
p2 = [3,4,5] # (12)→(21)→(12)→(22) # pen2 = 1;2, last2=2;2
q = paths_to_query(xgraph, p1, p2)
rel = @relation (pen1=p_1_1,pen2=p_2_2,last1=p_1_2,last2=p_2_3) begin
 x1(_id=init, e1=p_1_1, e3=p_2_1)
 x2(_id=p_1_1, e2=p_1_2)
 x2(_id=p_2_1, e4=p_2_2)
 x4(_id=p_2_2, e5=p_2_3)
end

# Empty path test
xg = graph_to_cset(Loop)()
add_parts!(xg, Symbol("x1"), 3)
set_subpart!(xg, Symbol("e1"), [2,1,3])
q = paths_to_query(Loop, [1],Int[])
rel = @relation (pen1=init,pen2=init,last1=p_1_1,last2=init) begin
 x1(_id=init, e1=p_1_1)
end
end # end of tests

#------------------------------------------------
# Back burner
#------------------------------------------------

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
                    change = true
                end
            end
        end
        # loop over commuting paths
        for (pth1, pth2) in c_paths
            src, tgt = G[:src][pth1[1]], G[:tgt][pth1[end]]
            for startval in 1:length(modl.tables[xs[src]])
                v1, v2 = startval, startval
                for e in pth1
                    v1 = modl[es[e]][v1]
                end
                for e in pth2
                    v2 = modl[es[e]][v2]
                end
                if v1 != v2
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