module TestFinCats

using Test, Catlab

# PreorderFinCats
#################
po1 = PreorderFinCat([(1,2)]) |> FinCat

po2 = PreorderFinCat([(1,2),(2,3)]) |> FinCat

F = FinDomFunctor(Dict(1=>1,2=>2),
  Dict(x=>x for x in hom_generators(po1)), po1, po2)

@test hom_map(F, 1=>1) == (1=>1)

# Categories on graphs
######################

# Free categories on graphs
g = parallel_arrows(Graph, 3)
C = FinCat(g)
@test Graph(C) == g
@test Graph(op(C)) == reverse(g)
@test Ob(C) == FinSet(2)
@test !is_discrete(C)
@test is_free(C)
# @test (hom(C, 1), hom_generator(C, 1)) == (Path(g, 1), 1)
@test ob_generators(C) == 1:2
@test hom_generators(C) == 1:3
@test startswith(sprint(show, C), "FinCat($(Graph)")
@test equations(C) == []

C_op = op(C)
@test C_op isa FinCat
# @test (ob(C_op, 1), ob_generator(C_op, 1)) == (1, 1)
# @test (hom(C_op, 1), hom_generator(C_op, 1)) == (Path(g, 1), 1)
@test ob_generators(C_op) == 1:2
@test hom_generators(C_op) == 1:3
@test op(C_op) == C
@test equations(C) == []

h = Graph(4)
add_edges!(h, [1,1,2,3], [2,3,4,4])
D = FinCat(h)
f = id(D, 2)
@test (src(f), tgt(f)) == (2, 2)
@test isempty(edges(f))
@test reverse(f) == f
g = compose(D, 1, 3)
@test edges(g) == [1,3]

D_op = op(D)
@test dom(D_op, 1) == 2
@test codom(D_op, 1) == 1
@test id(D_op, 2) == f
@test compose(D_op, 3, 1) == g

# Path equations
#---------------

# Simplex category truncated to one dimension.
Δ¹_graph = Graph(2)
add_edges!(Δ¹_graph, [1,1,2], [2,2,1])
Δ¹ = FinCat(Δ¹_graph, [ [1,3] => empty(Path, Δ¹_graph, 1),
                        [2,3] => empty(Path, Δ¹_graph, 1) ]);
Δ¹_op = op(Δ¹)
@test Graph(Δ¹) == Δ¹_graph
@test length(equations(Δ¹)) == 2
@test length(equations(Δ¹_op)) == 2
@test !is_free(Δ¹)
s = sprint(show, Δ¹)
@test startswith(s, "FinCat($(Graph)")
@test contains(s, "Path")

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
# @test Δ¹ isa FinCat{FreeCategory.Ob,FreeCategory.Hom} # No longer true
# @test ob(Δ¹, :V) == Simplex1D[:V]
# @test hom(Δ¹, :δ₀) == Simplex1D[:δ₀]
# @test ob_generator(Δ¹, :E) == Simplex1D[:E]
# @test hom_generator(Δ¹, :σ₀) == Simplex1D[:σ₀]
# @test ob_generator_name(Δ¹, Simplex1D[:V]) == :V
# @test hom_generator_name(Δ¹, Simplex1D[:δ₀]) == :δ₀
@test first.(ob_generators(Δ¹)) == [:V, :E]
@test first.(hom_generators(Δ¹)) == [:δ₀, :δ₁, :σ₀]
@test length(equations(Δ¹)) == 2
@test !is_free(Δ¹)
@test startswith(sprint(show, Δ¹), "FinCat(")

# Schemas as categories.
C = FinCat(SchWeightedGraph)
@test first.(ob_generators(C)) == [:V, :E, :Weight]
@test first.(hom_generators(C)) == [:src, :tgt, :weight]
g = path_graph(WeightedGraph{Float64}, 3, E=(weight=[0.5,1.5],))

#  NOT YET IMPLEMENTED: need to do C-Sets
# G = FinDomFunctor(g)
# @test is_functorial(G)
# @test ob_map(G, :Weight) == TypeSet(Float64)
# @test hom_map(G, :weight) == FinDomFunction([0.5, 1.5])

end
