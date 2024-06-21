module TestHomSearch 

using Test
using Catlab
using Random: seed!

# Setup
#######

seed!(100)

@present SchSetAttr(FreeSchema) begin
  X::Ob
  D::AttrType
  f::Attr(X,D)
end
@acset_type SetAttr(SchSetAttr)

# Finding C-set morphisms
#########################

# Graphs
#-------

g, h = path_graph(Graph, 3), path_graph(Graph, 4)
homs = [ACSetTransformation((V=[1,2,3], E=[1,2]), g, h),
        ACSetTransformation((V=[2,3,4], E=[2,3]), g, h)]
@test homomorphisms(g, h) == homs
@test homomorphisms(g, h, alg=HomomorphismQuery()) == homs
@test !is_isomorphic(g, h)

I = ob(terminal(Graph))
α = ACSetTransformation((V=[1,1,1], E=[1,1]), g, I)
@test homomorphism(g, I) == α
@test homomorphism(g, I, alg=HomomorphismQuery()) == α
@test !is_homomorphic(g, I, monic=true)
@test !is_homomorphic(I, h)
@test !is_homomorphic(I, h, alg=HomomorphismQuery())

# Graph homomorphism starting from partial assignment, e.g. vertex assignment.
α = ACSetTransformation((V=[2,3,4], E=[2,3]), g, h)
@test homomorphisms(g, h, initial=(V=[2,3,4],)) == [α]
@test homomorphisms(g, h, initial=(V=Dict(1 => 2, 3 => 4),)) == [α]
@test homomorphisms(g, h, initial=(E=Dict(1 => 2),)) == [α]
# Inconsistent initial assignment.
@test !is_homomorphic(g, h, initial=(V=Dict(1 => 1), E=Dict(1 => 3)))
# Consistent initial assignment but no extension to complete assignment.
@test !is_homomorphic(g, h, initial=(V=Dict(1 => 2, 3 => 3),))

# Monic and iso on a componentwise basis.
g1, g2 = path_graph(Graph, 3), path_graph(Graph, 2)
add_edges!(g1, [1,2,3,2], [1,2,3,3])  # loops on each node and one double arrow
add_edge!(g2, 1, 2)  # double arrow
@test length(homomorphisms(g2, g1)) == 8 # each vertex + 1->2, and four for 2->3
@test length(homomorphisms(g2, g1, monic=[:V])) == 5 # remove vertex solutions
@test length(homomorphisms(g2, g1, monic=[:E])) == 2 # two for 2->3
@test length(homomorphisms(g2, g1, iso=[:E])) == 0

# valid constraint
@test length(homomorphisms(g2, g1; predicates=(V=Dict([1 => [1,3]]),))) == 3
@test length(homomorphisms(g2, g1; predicates=(E=Dict([1 => [1,3]]),))) == 2

# Loose
s1 = SetAttr{Int}()
add_part!(s1, :X, f=1)
add_part!(s1, :X, f=1)
s2, s3 = deepcopy(s1), deepcopy(s1)
set_subpart!(s2, :f, [2,1])
set_subpart!(s3, :f, [20,10])
@test length(homomorphisms(s2,s3))==0
@test length(homomorphisms(s2,s3; type_components=(D=x->10*x,)))==1
@test homomorphism(s2,s3; type_components=(D=x->10*x,)) isa LooseACSetTransformation
@test length(homomorphisms(s1,s1; type_components=(D=x->x^x,)))==4

#Backtracking with monic and iso failure objects
g1, g2 = path_graph(Graph, 3), path_graph(Graph, 2)
rem_part!(g1,:E,2)
@test_throws ErrorException homomorphism(g1,g2;monic=true,error_failures=true)

# Epic constraint
g0, g1, g2 = Graph(2), Graph(2), Graph(2)
add_edges!(g0, [1,1],[1,2]) # ↻•→•
add_edges!(g1, [1,1],[2,2]) # •⇉•
add_edges!(g2, [1,1,1],[1,1,2]) # ↻↻•→•
@test length(homomorphisms(g1, g2, epic=[:V])) == 1
@test length(homomorphisms(g1, g2, epic=[:E])) == 0
@test length(homomorphisms(g2, g0, epic=[:E])) == 1
@test length(homomorphisms(g2, g0, epic=[:V])) == 1

g3, g4 = path_graph(Graph,3), path_graph(Graph,4)
add_edges!(g3,[1,3],[1,3])  # g3: ↻•→•→• ↺
@test length(homomorphisms(g4,g3)) == 6 # 2 for each: 1/2/3 edges sent to loop
@test length(homomorphisms(g4,g3; epic=[:V])) == 2 # send only one edge to loop
@test length(homomorphisms(g4,g3; epic=[:E])) == 0 # only have 3 edges to map

@test length(homomorphisms(Graph(4),Graph(2); epic=true)) == 14 # 2^4 - 2

# Symmetric graphs
#-----------------

g, h = path_graph(SymmetricGraph, 4), path_graph(SymmetricGraph, 4)
αs = homomorphisms(g, h)
@test all(is_natural(α) for α in αs)
@test length(αs) == 16
αs = isomorphisms(g, h)
@test length(αs) == 2
@test map(α -> collect(α[:V]), αs) == [[1,2,3,4], [4,3,2,1]]
g = path_graph(SymmetricGraph, 3)
@test length(homomorphisms(g, h, monic=true)) == 4

# Graph colorability via symmetric graph homomorphism.
# The 5-cycle has chromatic number 3 but the 6-cycle has chromatic number 2.
K₂, K₃ = complete_graph(SymmetricGraph, 2), complete_graph(SymmetricGraph, 3)
C₅, C₆ = cycle_graph(SymmetricGraph, 5), cycle_graph(SymmetricGraph, 6)
@test !is_homomorphic(C₅, K₂)
@test is_homomorphic(C₅, K₃)
@test is_natural(homomorphism(C₅, K₃))
@test is_homomorphic(C₆, K₂)
@test is_natural(homomorphism(C₆, K₂))

# Labeled graphs
#---------------

g = cycle_graph(LabeledGraph{Symbol}, 4, V=(label=[:a,:b,:c,:d],))
h = cycle_graph(LabeledGraph{Symbol}, 4, V=(label=[:c,:d,:a,:b],))
α = ACSetTransformation((V=[3,4,1,2], E=[3,4,1,2]), g, h)
@test homomorphism(g, h) == α
@test homomorphism(g, h, alg=HomomorphismQuery()) == α
h = cycle_graph(LabeledGraph{Symbol}, 4, V=(label=[:a,:b,:d,:c],))
@test !is_homomorphic(g, h)
@test !is_homomorphic(g, h, alg=HomomorphismQuery())

# Random
#-------

comps(x) = sort([k=>collect(v) for (k,v) in pairs(components(x))])
# same set of morphisms
K₆ = complete_graph(SymmetricGraph, 6)
hs = homomorphisms(K₆,K₆)
rand_hs = homomorphisms(K₆,K₆; random=true)
@test sort(hs,by=comps) == sort(rand_hs,by=comps) # equal up to order
@test hs != rand_hs # not equal given order
@test homomorphism(K₆,K₆) != homomorphism(K₆,K₆;random=true)

# As a macro
#-----------

g = cycle_graph(LabeledGraph{String}, 4, V=(label=["a","b","c","d"],))
h = cycle_graph(LabeledGraph{String}, 4, V=(label=["b","c","d","a"],))
α = @acset_transformation g h
β = @acset_transformation g h begin
  V = [4,1,2,3]
  E = [4,1,2,3]
end monic=true
γ = @acset_transformation g h begin end monic=[:V]
@test α[:V](1) == 4
@test α[:E](1) == 4
@test α == β == γ

x = @acset Graph begin
  V = 2
  E = 2
  src = [1,1]
  tgt = [2,2]
end
@test length(@acset_transformations x x) == length(@acset_transformations x x monic=[:V]) == 4
@test length(@acset_transformations x x monic = true) == 2
@test length(@acset_transformations x x begin V=[1,2] end monic = [:E]) == 2
@test length(@acset_transformations x x begin V = Dict(1=>1) end monic = [:E]) == 2
@test_throws ErrorException @acset_transformation g h begin V = [4,3,2,1]; E = [1,2,3,4] end


# VM search
#----------
@present SchDDS(FreeSchema) begin
  X::Ob
  Φ::Hom(X,X)
end
@acset_type DDS(SchDDS, index=[:Φ])

# Look for path graph
#--------------------
g = path_graph(Graph, 3)
h = erdos_renyi(Graph, 100, 0.05)

@test_throws ErrorException compile_hom_search(g, strat=:xxxxxx);
prog1 = compile_hom_search(g, strat=:neighbor)
prog2 = compile_hom_search(g, strat=:connected)

@test sprint(show, prog1) isa String

expected = length(homomorphisms(g, h))
@test all(==(expected), map([prog1,prog2]) do prog 
  length(homomorphisms(g, h; alg=VMSearch(), prog))
end)

# Random VM 
prog3 = compile_hom_search(g, strat=:random)
h = erdos_renyi(Graph, 20, 0.05) # small, b/c random can be very inefficient
@test length(homomorphisms(g,h; alg=VMSearch(), prog=prog3)) == length(homomorphisms(g,h))


# DDS 
#-----
DDS(i::Int) = @acset DDS begin X=i; Φ=[rand(1:i) for _ in 1:i] end # random DDS

for _ in 1:10
  g, h = DDS.([10,150])
  prog1 = compile_hom_search(g, strat=:neighbor);
  prog2 = compile_hom_search(g, strat=:connected);

  expected = length(homomorphisms(g, h))
  @test all(==(expected), map([prog1,prog2]) do prog 
    length(homomorphisms(g, h; alg=VMSearch(), prog))
  end)
end

# Enumeration of subobjects 
###########################

G = path_graph(Graph, 3)
subG, subobjs = subobject_graph(G)
@test length(subobjs) == 13 # ⊤,2x •→• •,2x •→•, •••,3x ••, 3x •, ⊥
@test length(incident(subG, 13, :src)) == 13 # ⊥ is initial
@test length(incident(subG, 1, :src)) == 1 # ⊤ is terminal

# With attributes
G′ = path_graph(WeightedGraph{Bool}, 3)
G′[:weight] = [false, AttrVar(add_part!(G′, :Weight))]
subG′, subobjs′ = subobject_graph(G′)
@test is_isomorphic(subG, subG′)
@test nparts(dom(hom(first(subobjs′))), :Weight) == 1
@test nparts(dom(hom(last(subobjs′))), :Weight) == 0

# Graph and ReflexiveGraph should have same subobject structure
subG2, _ = subobject_graph(path_graph(Graph, 2))
subRG2, sos = subobject_graph(path_graph(ReflexiveGraph, 2))
@test all(is_natural, hom.(sos))
@test is_isomorphic(subG2, subRG2)

# Partial overlaps 
G, H = path_graph.(Graph, 2:3)
os = collect(partial_overlaps(G, G))
@test length(os) == 7 # ⊤, ••, 4× •, ⊥

po = partial_overlaps([G, H])
@test length(collect(po))==12  # 2×⊤, 3×••, 6× •, ⊥
@test all(m -> apex(m) == G, Iterators.take(po, 2)) # first two are •→•
@test all(m -> apex(m) == Graph(2), 
          Iterators.take(Iterators.drop(po, 2), 3)) # next three are • •

# Partial overlaps with attributes 

@present SchVELabeledGraph <: SchGraph begin
  VL::AttrType; EL::AttrType; vlabel::Attr(V,VL); elabel::Attr(E,EL)
end

@acset_type VELabeledGraph(SchVELabeledGraph) <: AbstractGraph
const LGraph = VELabeledGraph{Bool,Bool}

G = @acset LGraph begin 
  V=3; E=2; src=[1,2]; tgt=[2,3]; vlabel=Bool[0,1,1]; elabel=Bool[0,1]
end
H = @acset LGraph begin 
  V=3; E=2; src=[1,2]; tgt=[2,3]; vlabel=Bool[0,0,1]; elabel=Bool[0,0]
end
os = partial_overlaps(G, H); # abstract=true
@test count(apx->nparts(apx,:E)==2, apex.(os)) == 1
os = partial_overlaps(G, H; abstract=[:VL]);
@test count(apx->nparts(apx,:E)==2, apex.(os)) == 0
@test count(apx->nparts(apx,:E)==1, apex.(os)) == 4
os = partial_overlaps(G, H; abstract=false);
@test count(apx->nparts(apx,:E)==2, apex.(os)) == 0
@test count(apx->nparts(apx,:E)==1, apex.(os)) == 1

# Maximum Common C-Set
######################
const WG = WeightedGraph{Bool}
"""
Searching for overlaps: •→•→•↺  vs ↻•→•→•
Two results: •→•→• || •↺ •→• 
"""
g1 = @acset WG begin 
  V=3; E=3; src=[1,1,2]; tgt=[1,2,3]; weight=[true,false,false]
end
g2 = @acset WG begin 
  V=3; E=3; src=[1,2,3]; tgt=[2,3,3]; weight=[true,false,false] 
end
apex1 = @acset WG begin
  V=3; E=2; Weight=2; src=[1,2]; tgt=[2,3]; weight=AttrVar.(1:2)
end
apex2 = @acset WG begin 
  V=3; E=2; Weight=2; src=[1,3]; tgt=[2,3]; weight=AttrVar.(1:2)
end

results = collect(maximum_common_subobject(g1, g2))
@test length(results) == 2
is_iso1 = map(result -> is_isomorphic(first(result), apex1), results)
@test sum(is_iso1) == 1
results = first(is_iso1) ? results : reverse(results)
(apx1,((L1,R1),)), (apx2,((L2,R2),)) = results
@test collect(L1[:V]) == [1,2,3]
@test collect(R1[:V]) == [1,2,3]
@test L1(apx1) == Subobject(g1, V=[1,2,3], E=[2,3])

@test is_isomorphic(apx2, apex2)
@test collect(L2[:V]) == [1,2,3]
@test collect(R2[:V]) == [3,1,2]
@test L2(apx2) == Subobject(g1, V=[1,2,3], E=[1,3])

# If we demand equality on attributes, max overlap is one false edge and all vertices.
exp = @acset WG begin V=3; E=1; src=1; tgt=2; weight=[false] end
@test first(first(maximum_common_subobject(g1, g2; abstract=false))) == exp

# Mark as deleted
#################
@acset_type AbsMADGraph(SchWeightedGraph, part_type=BitSetParts) <: AbstractGraph
const MADGraph = AbsMADGraph{Symbol}

v1, v2 = MADGraph.(1:2)
@test !is_isomorphic(v1,v2)
rem_part!(v2, :V, 1)
@test is_isomorphic(v1,v2)
@test is_isomorphic(v2,v1)


end # module
