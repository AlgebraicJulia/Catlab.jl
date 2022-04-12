module TestFinCats
using Test

using Catlab, Catlab.Theories, Catlab.CategoricalAlgebra, Catlab.Graphs
using Catlab.Graphs.BasicGraphs: TheoryGraph, TheoryReflexiveGraph,
  TheoryWeightedGraph

# Categories on graphs
######################

# Free categories
g = parallel_arrows(Graph, 3)
C = FinCat(g)
@test graph(C) == g
@test Ob(C) == FinSet(2)
@test !is_discrete(C)
@test is_free(C)
@test hom(C, 1) == Path(g, 1)
@test ob_generators(C) == 1:2
@test hom_generators(C) == 1:3
@test startswith(sprint(show, C), "FinCat($(Graph)")

h = Graph(4)
add_edges!(h, [1,1,2,3], [2,3,4,4])
D = FinCat(h)
f = id(D, 2)
@test (src(f), tgt(f)) == (2, 2)
@test isempty(edges(f))
f = compose(D, 1, 3)
@test edges(f) == [1,3]

# Functors between free categories.
C = FinCat(parallel_arrows(Graph, 2))
F = FinFunctor((V=[1,4], E=[[1,3], [2,4]]), C, D)
@test dom(F) == C
@test codom(F) == D
@test is_functorial(F)
@test Ob(F) == FinFunction([1,4], FinSet(4))
@test startswith(sprint(show, F), "FinFunctor($([1,4]),")

@test ob_map(F, 2) == 4
@test hom_map(F, 1) == Path(h, [1,3])
@test collect_ob(F) == [1,4]
@test collect_hom(F) == [Path(h, [1,3]), Path(h, [2,4])]

# Composition of functors.
g, h, k = path_graph(Graph, 2), path_graph(Graph, 3), path_graph(Graph, 5)
C, D, E = FinCat(g), FinCat(h), FinCat(k)
F = FinFunctor([1,3], [[1,2]], C, D)
G = FinFunctor([1,3,5], [[1,2],[3,4]], D, E)
@test is_functorial(G)
@test hom_map(G, Path(h, [1,2])) == Path(k, [1,2,3,4])
@test F⋅G == FinFunctor([1,5], [[1,2,3,4]], C, E)
@test id(C)⋅F == F
@test F⋅id(D) == F

# Functors out free categories.
C = FinCat(parallel_arrows(Graph, 2))
f, g = FinFunction([1,3], 3), FinFunction([2,3], 3)
F = FinDomFunctor([FinSet(2), FinSet(3)], [f,g], C)
@test is_functorial(F)
@test dom(F) == C
@test codom(F) isa TypeCat{<:FinSet{Int},<:FinFunction{Int}}
@test startswith(sprint(show, F), "FinDomFunctor(")

@test ob_map(F, 1) == FinSet(2)
@test hom_map(F, 2) == g

# Commutative square as natural transformation.
C = FinCat(path_graph(Graph, 2))
F = FinDomFunctor([FinSet(4), FinSet(2)], [FinFunction([1,1,2,2])], C)
α₀, α₁ = FinFunction([3,4,1,2]), FinFunction([2,1])
α = FinTransformation([α₀, α₁], F, F)
@test is_natural(α)
@test (α[1], α[2]) == (α₀, α₁)
@test components(α) == [α₀, α₁]
@test α⋅α == FinTransformation([FinFunction(1:4), FinFunction(1:2)], F, F)

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
@test ob(Δ¹, :V) isa FreeCategory.Ob
@test hom(Δ¹, :δ₀) isa FreeCategory.Hom
@test first.(ob_generators(Δ¹)) == [:V, :E]
@test first.(hom_generators(Δ¹)) == [:δ₀, :δ₁, :σ₀]
@test length(equations(Δ¹)) == 2
@test !is_free(Δ¹)
@test startswith(sprint(show, Δ¹), "FinCat(")

# Graph as set-valued functor on a free category.
F = FinDomFunctor(path_graph(Graph, 3))
C = dom(F)
@test C == FinCat(TheoryGraph)
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
                       TheoryGraph, TheoryReflexiveGraph),
            G_refl, strict=false)
@test dom(G) == FinCat(TheoryGraph)
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

σ = FinTransformation(G, G, V=id(FinSet(2)), E=FinFunction([2,1,4,3]))
@test σ⋅σ == FinTransformation(G, G, V=id(FinSet(2)), E=FinFunction(1:4))
@test α⋅σ == FinTransformation(F, G, V=FinFunction([1,2,2]), E=FinFunction([2,4]))

# Pullback data migration by pre-whiskering.
ιV = FinFunctor([:V], FinCat(1), FinCat(TheoryGraph))
αV = ιV * α
@test ob_map(dom(αV), 1) == ob_map(F, :V)
@test ob_map(codom(αV), 1) == ob_map(G, :V)
@test component(αV, 1) == component(α, :V)

# Post-whiskering and horizontal composition.
ιE = FinFunctor([:E], FinCat(1), FinCat(TheoryGraph))
ϕ = FinTransformation([:src], ιE, ιV)
@test is_natural(ϕ)
@test component(ϕ*F, 1) == hom_map(F, :src)
@test component(ϕ*α, 1) == hom_map(F, :src) ⋅ α[:V]

# Schemas as categories.
C = FinCat(TheoryWeightedGraph)
@test first.(ob_generators(C)) == [:V, :E, :Weight]
@test first.(hom_generators(C)) == [:src, :tgt, :weight]
g = path_graph(WeightedGraph{Float64}, 3, E=(weight=[0.5,1.5],))
G = FinDomFunctor(g)
@test is_functorial(G)
@test ob_map(G, :Weight) == TypeSet(Float64)
@test hom_map(G, :weight) == FinDomFunction([0.5, 1.5])

# Initiality of functors
########################

"Commutative square diagram: with 1→2→4 and 1→3→4"
S = FinCat(@acset Graph begin
  V = 4
  E = 4
  src = [1,1,2,3]
  tgt = [2,3,4,4]
end)

"Equalizer diagram: 1→2⇉3"
T = FinCat(@acset Graph begin
  V = 3
  E = 3
  src = [1,2,2]
  tgt = [2,3,3]
end)

"Extra bit added to beginning equalizer diagram: 4→1→2⇉3"
T2 = FinCat(@acset Graph begin
  V = 4
  E = 4
  src = [1,2,2,4]
  tgt = [2,3,3,1]
end)

"Extra bit added to end of equalizer diagram: 1→2⇉3→4"
T3 = FinCat(@acset Graph begin
  V = 4
  E = 4
  src = [1,2,2,3]
  tgt = [2,3,3,4]
end)


# Opposite square corners folded on top of each other
F1 = FinFunctor([1,2,2,3], [1,1,2,3], S, T)

# Both paths in square get mapped onto single length-2 path in equalizer
F2 = FinFunctor([1,2,2,3], [1,1,2,2], S, T)

# Fit equalizer into square, ignoring opposite corner
F3 = FinFunctor([1,2,4], [1,3,3], T, S)

# Same as F1, but there is an additional piece of data in codomain, ignored
F4 = FinFunctor([1,2,3], [1,2,3], T, T2)

# Same as F1, but there is an additional piece of data in codomain, ignored
F5 = FinFunctor([1,2,3], [1,2,3], T, T2)


@test all(is_functorial.([F1,F2,F3,F4]))
@test is_initial(F1)
@test !is_initial(F2)
@test !is_initial(F3)
@test !is_initial(F4)
@test !is_initial(F5)

# Define examples for limits and colimits
#----------------------------------------
@present I_(FreeSchema) begin (I1, I2)::Ob; i::Hom(I1, I2) end
@present M_(FreeSchema) begin (M1, M2)::Ob; m::Hom(M1, M2) end
@present N_(FreeSchema) begin (N1, N2)::Ob; n::Hom(N1, N2) end
@present J_(FreeSchema) begin
  (J1, J2, J3)::Ob; j1::Hom(J1, J2); j2::Hom(J3,J2)
end
@present K_(FreeSchema) begin
  K::Ob; k::Hom(K,K)
  compose(k,k) == k
end

I, J, K, M, N = FinCat.([I_,J_,K_,M_,N_]);
(i,),(j1,j2),(k_,) = hom_generators.([I,J,K])

F_IJ = FinDomFunctor(Dict(:I1=>:J1, :I2=>:J2), Dict(:i=>:j1), I, J)
G_IJ = FinDomFunctor(Dict(:I1=>:J3, :I2=>:J2), Dict(:i=>:j2), I, J)
F_IK = FinDomFunctor(Dict(:I1=>:K, :I2=>:K), Dict(:i=>:k), I, K)
J_I = FinDomFunctor(Dict(:J1=>:I1, :J2=>:I2, :J3 => :I1),
                    Dict(:j1=>:i, :j2=>:i), J, I)

# Limits
#-------
p = product([I, J, K]);
e = equalizer([F_IJ, G_IJ])
e2 = equalizer([F_IJ, F_IJ])

map([p, e, e2]) do lim
  @test all(is_functorial.(legs(lim)))
end

u = universal(p, Multispan([id(I), F_IJ, F_IK]))
@test is_functorial(u)
ij1k,i2j1k,i2j2k = [h for h in hom_generators(apex(p)) if h.args[1] in Symbol.(
  ["(i, id(J1), id(K))","(id(I2), j1, id(K))","(id(I2), id(J2), k)"])]
@test hom_map(u, :i) == compose(ij1k, i2j1k, i2j2k)

u = universal(e2, J_I)
@test is_functorial(u)

# encode a graph homomorphism as a FinCat. It is •→• ⟶ Grph
# by curry adjunction, the shape is the product of •→• and •⇉•
P = apex(product([I, FinCat(TheoryGraph)]))
@test length(equations(P)) == 2 # the two naturality squares
P = apex(product([I,M,N])) # multidimensional
@test length(equations(P)) == 6
P = apex(product([I,K])) # base equation in K gets multiplied by 2
@test length(equations(P)) == 3 # also have one naturality square


# Colimits
#---------
cp = coproduct([I, I, J]);
@test length(ob_generators(apex(cp))) == 7
cp2 = coproduct([K, K])
@test length(equations(apex(cp2))) == 2
ce1 = coequalizer([G_IJ, G_IJ]);
ce2 = coequalizer([F_IJ, G_IJ]);
map([cp, ce1, ce2]) do colim
  @test all(is_functorial.(legs(colim)))
end

u = universal(cp, Multicospan([F_IJ, G_IJ, id(J)]))
@test is_functorial(u)
@test ob_map(u, Symbol("I1#1")) == ob_generators(J)[1]
@test ob_map(u, Symbol("I1#2")) == ob_generators(J)[3]

u = universal(ce1, J_I)
@test is_functorial(u)

end
