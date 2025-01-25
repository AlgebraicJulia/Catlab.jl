module TestFinCats

using Test, Catlab

# Categories on graphs
######################

# Free categories on graphs
g = parallel_arrows(Graph, 3)
C = FinCat(g)
@test graph(C) == g
@test graph(op(C)) == reverse(g)
@test !is_discrete(C)
@test is_free(C)
@test (hom(C, 1), hom_generator(C, 1)) == (Path(g, 1), 1)
@test ob_generators(C) == 1:2
@test hom_generators(C) == 1:3
@test startswith(sprint(show, C), "FinCat($(Graph)")
@test equations(C) == []

C_op = op(C)
@test C_op isa FinCat
@test (ob(C_op, 1), ob_generator(C_op, 1)) == (1, 1)
@test (hom(C_op, 1), hom_generator(C_op, 1)) == (Path(g, 1), 1)
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
                        [2,3] => empty(Path, Δ¹_graph, 1) ])
Δ¹_op = op(Δ¹)
@test graph(Δ¹) == Δ¹_graph
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
@test Δ¹ isa FinCat{FreeCategory.Ob,FreeCategory.Hom}
@test ob(Δ¹, :V) == Simplex1D[:V]
@test hom(Δ¹, :δ₀) == Simplex1D[:δ₀]
@test ob_generator(Δ¹, :E) == Simplex1D[:E]
@test hom_generator(Δ¹, :σ₀) == Simplex1D[:σ₀]
@test ob_generator_name(Δ¹, Simplex1D[:V]) == :V
@test hom_generator_name(Δ¹, Simplex1D[:δ₀]) == :δ₀
@test first.(ob_generators(Δ¹)) == [:V, :E]
@test first.(hom_generators(Δ¹)) == [:δ₀, :δ₁, :σ₀]
@test length(equations(Δ¹)) == 2
@test !is_free(Δ¹)
@test startswith(sprint(show, Δ¹), "FinCat(")

# Graph as set-valued functor on a free category.
F = FinDomFunctor(path_graph(Graph, 3))
C = dom(F)
@test C == FinCat(SchGraph)
@test is_functorial(F)
@test ob_map(F, :V) == FinSet(3)
@test hom_map(F, :src) == FinFunction([1,2], 3)
@test F(ob(C, :E)) == FinSet(2)
@test F(hom(C, :tgt)) == FinFunction([2,3], 3)
@test F(id(ob(C, :E))) == id(FinSet(2))

# Reflexive graph as set-valued functor on a category with equations.
G_refl = FinDomFunctor(path_graph(ReflexiveGraph, 3))
@test is_functorial(G_refl)
G = compose(FinFunctor(Dict(:V=>:V, :E=>:E), Dict(:src=>:src, :tgt=>:tgt),
                       SchGraph, SchReflexiveGraph),
            G_refl)
@test dom(G) == FinCat(SchGraph)
@test codom(G) == codom(G_refl)
@test ob_map(G, :V) == FinSet(3)
@test hom_map(G, :src) isa FinFunction{Int}
@test startswith(sprint(show, G), "compose(")

# Graph homomorphisms as natural transformations.
g = parallel_arrows(Graph, 2)
add_edges!(g, [2,2], [2,2])
G = FinDomFunctor(g)
α = FinTransformation(F, G, V=FinFunction([1,2,2]), E=FinFunction([1,3],4))
@test dom_ob(α) == C
@test codom_ob(α) isa TypeCat{<:SetOb,<:FinDomFunction{Int}}
@test is_natural(α)
@test α[:V](3) == 2
@test startswith(sprint(show, α), "FinTransformation(")

α_op = op(α)
@test α_op isa FinTransformationMap
@test dom(α_op) == op(G)
@test codom(α_op) == op(F)
@test op(α_op) == α

σ = FinTransformation(G, G, V=id(FinSet(2)), E=FinFunction([2,1,4,3]))
@test σ⋅σ == FinTransformation(G, G, V=id(FinSet(2)), E=FinFunction(1:4))
@test α⋅σ == FinTransformation(F, G, V=FinFunction([1,2,2]), E=FinFunction([2,4]))

# Pullback data migration by pre-whiskering.
ιV = FinFunctor([:V], FinCat(1), FinCat(SchGraph))
αV = ιV * α
@test ob_map(dom(αV), 1) == ob_map(F, :V)
@test ob_map(codom(αV), 1) == ob_map(G, :V)
@test component(αV, 1) == component(α, :V)

# Post-whiskering and horizontal composition.
ιE = FinFunctor([:E], FinCat(1), FinCat(SchGraph))
ϕ = FinTransformation([:src], ιE, ιV)
@test is_natural(ϕ)
@test component(ϕ*F, 1) == hom_map(F, :src)
@test component(ϕ*α, 1) == hom_map(F, :src) ⋅ α[:V]

# Schemas as categories.
C = FinCat(SchWeightedGraph)
@test first.(ob_generators(C)) == [:V, :E, :Weight]
@test first.(hom_generators(C)) == [:src, :tgt, :weight]
g = path_graph(WeightedGraph{Float64}, 3, E=(weight=[0.5,1.5],))
G = FinDomFunctor(g)
@test is_functorial(G)
@test ob_map(G, :Weight) == TypeSet(Float64)
@test hom_map(G, :weight) == FinDomFunction([0.5, 1.5])

end
