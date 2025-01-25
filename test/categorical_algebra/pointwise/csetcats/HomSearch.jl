module TestCSetHomSearch 

using Test, Catlab
using Random: seed!

# Setup
#######

seed!(10)


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


# Backtracking with monic and iso failure objects
g1, g2 = path_graph(Graph, 3), path_graph(Graph, 2)
rem_part!(g1,:E,2)
@test_throws ErrorException homomorphism(g1, g2; monic=true, error_failures=true)


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

# taking a particular number of morphisms 
@test length(homomorphisms(Graph(4),Graph(2); epic=true, take=7)) == 7

# throwing an error if max is exceeded 
@test_throws ErrorException homomorphism(Graph(1), Graph(2))
@test_throws ErrorException length(homomorphisms(Graph(4),Graph(2); epic=true, max=6))
@test length(homomorphisms(Graph(4),Graph(2); epic=true, max=16)) == 14

# filtering morphisms
@test (length(homomorphisms(Graph(3),Graph(5); filter=is_monic))
      == length(homomorphisms(Graph(3),Graph(5); monic=true)))

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
@test is_natural(homomorphism(C₅, K₃; any=true))
@test is_homomorphic(C₆, K₂)
@test is_natural(homomorphism(C₆, K₂; any=true))


# Random
#-------

comps(x) = sort([k=>collect(v) for (k,v) in pairs(components(x))])
# same set of morphisms
K₆ = complete_graph(SymmetricGraph, 6)
hs = homomorphisms(K₆,K₆)
rand_hs = homomorphisms(K₆,K₆; random=true)
@test sort(hs,by=comps) == sort(rand_hs,by=comps) # equal up to order
@test hs != rand_hs # not equal given order

# This is very probably true
@test (homomorphism(K₆, K₆, any=true) 
      != homomorphism(K₆ ,K₆; any=true, random=true))

# As a macro
############

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

# DynamicACsets
###############
G, H = [DynamicACSet("Grph",SchGraph) for _ in 1:2];
add_parts!(G, :V, 2); 
add_parts!(H,:V,2);
add_part!(G, :E; src=1, tgt=2)
add_parts!(H, :E,2; src=[1,2], tgt=[1,2])

@test is_natural(id(G))

hs = homomorphisms(G,H)
@test length(hs) == 2
@test all(is_natural, hs)

end # module
