module TestFinCats
using Test

using Catlab, Catlab.CategoricalAlgebra, Catlab.Graphs
using Catlab.Theories: FreeCategory
using Catlab.Graphs.BasicGraphs: TheoryGraph

# Categories on graphs
######################

# Free categories
#----------------

g = parallel_arrows(Graph, 3)
C = FinCat(g)
@test graph(C) == g
@test Ob(C) == FinSet(2)
@test is_free(C)
@test hom(C, 1) == Path(g, 1)
@test ob_generators(C) == 1:2
@test hom_generators(C) == 1:3

h = Graph(4)
add_edges!(h, [1,1,2,3], [2,3,4,4])
D = FinCat(h)
f = id(D, 2)
@test (src(f), tgt(f)) == (2, 2)
@test isempty(edges(f))
f = compose(D, 1, 3)
@test edges(f) == [1,3]

C = FinCat(parallel_arrows(Graph, 2))
F = FinFunctor((V=[1,4], E=[[1,3], [2,4]]), C, D)
@test dom(F) == C
@test codom(F) == D
@test is_functorial(F)
@test Ob(F) == FinFunction([1,4], FinSet(4))

@test ob_map(F, 2) == 4
@test hom_map(F, 1) == Path(h, [1,3])
@test collect_ob(F) == [1,4]
@test collect_hom(F) == [Path(h, [1,3]), Path(h, [2,4])]

g, h = path_graph(Graph, 3), path_graph(Graph, 5)
C, D = FinCat(g), FinCat(h)
F = FinFunctor([1,3,5], [[1,2],[3,4]], C, D)
@test is_functorial(F)
@test hom_map(F, Path(g, [1,2])) == Path(h, [1,2,3,4])

# Commutative square as natural transformation.
C = FinCat(path_graph(Graph, 2))
F = FinDomFunctor([FinSet(4), FinSet(2)], [FinFunction([1,1,2,2])], C)
α₀, α₁ = FinFunction([3,4,1,2]), FinFunction([2,1])
α = FinNatTransformation([α₀, α₁], F, F)
@test is_natural(α)
@test (α[1], α[2]) == (α₀, α₁)
@test components(α) == [α₀, α₁]

# Free diagrams
#--------------

C = FinCat(parallel_arrows(Graph, 2))
f, g = FinFunction([1,3], 3), FinFunction([2,3], 3)
F = FinDomFunctor([FinSet(2), FinSet(3)], [f,g], C)
@test is_functorial(F)
@test dom(F) == C
@test codom(F) isa TypeCat{<:FinSet{Int},<:FinFunction{Int}}
@test ob_map(F, 1) == FinSet(2)
@test hom_map(F, 2) == g

# `FreeDiagrams` interop.
diagram = FreeDiagram(ParallelPair(f, g))
@test FreeDiagram(F) == diagram
@test FinDomFunctor(diagram) == F

# Diagram interface.
@test diagram_type(F) <: Tuple{FinSet{Int},FinFunction{Int}}
@test cone_objects(F) == [FinSet(2), FinSet(3)]
@test cocone_objects(F) == [FinSet(2), FinSet(3)]
@test ob(limit(F)) == FinSet(1)
@test ob(colimit(F)) == FinSet(2)

# Path equations
#---------------

# Simplex category truncated to one dimension.
Δ¹_graph = Graph(2)
add_edges!(Δ¹_graph, [1,1,2], [2,2,1])
Δ¹ = FinCat(Δ¹_graph, [ [1,3] => empty(Path, Δ¹_graph, 1),
                        [2,3] => empty(Path, Δ¹_graph, 1) ])
@test graph(Δ¹) == Δ¹_graph
@test length(equations(Δ¹)) == 2
@test !is_free(Δ¹)

# Symbolic categories
#####################

@present Simplex1D(FreeCategory) begin
  (V, E)::Ob
  (δ₀, δ₁)::Hom(V, E)
  σ₀::Hom(E, V)

  δ₀ ⋅ σ₀ == id(V)
  δ₁ ⋅ σ₀ == id(V)
end

Δ¹ = FinCat(Simplex1D)
@test Δ¹ isa FinCat{FreeCategory.Ob,FreeCategory.Hom}
@test ob(Δ¹, :V) isa FreeCategory.Ob
@test hom(Δ¹, :δ₀) isa FreeCategory.Hom
@test first.(ob_generators(Δ¹)) == [:V, :E]
@test first.(hom_generators(Δ¹)) == [:δ₀, :δ₁, :σ₀]
@test length(equations(Δ¹)) == 2
@test !is_free(Δ¹)

# Graph as set-valued functor on the theory of graphs.
g = path_graph(Graph, 3)
F = FinDomFunctor(TheoryGraph, g)
C = dom(F)
@test is_functorial(F)
@test ob_map(F, :V) == FinSet(3)
@test hom_map(F, :src) == FinFunction([1,2], 3)
@test F(ob(C, :E)) == FinSet(2)
@test F(hom(C, :tgt)) == FinFunction([2,3], 3)
@test F(id(ob(C, :E))) == id(FinSet(2))

# Graph homomorphism as natural transformation.
h = path_graph(Graph, 2)
add_edge!(h, 2, 2)
G = FinDomFunctor(TheoryGraph, h)
α = FinNatTransformation(F, G, V=FinFunction([1,2,2]), E=FinFunction([1,2]))
@test dom_ob(α) == C
@test codom_ob(α) isa TypeCat{<:FinSet{Int},<:FinFunction{Int}}
@test is_natural(α)
@test α[:V](3) == 2

end
