module TestFinFunctors 

using Test, Catlab, ACSets

h = Graph(4)
add_edges!(h, [1,1,2,3], [2,3,4,4])
D = FinCat(h)

# Functors between free categories.

C = FinCat(parallel_arrows(Graph, 2))
F = FinDomFunctor((V=[1,4], E=[[1,3], [2,4]]), C, D)
G = FinDomFunctor((V=[2,1], E=[[1],[2]]), C, C)
@test dom(F) == C
@test codom(F) == Cat(D)
@test is_functorial(F)
@test !is_functorial(G)
@test map(collect,functoriality_failures(G)) == ([1,2],[1,2],[])
@test U_CatSet(F) == FinFunction([1,4], FinSet(4))
# @test startswith(sprint(show, F), "FinFunctor($([1,4]),")
@test ob_map(F, 2) == 4
@test gen_map(F, 1) == Path(h, [1,3])
@test collect_ob(F) == [1,4]
@test collect_hom(F) == [Path(h, [1,3]), Path(h, [2,4])]

F_op = op(F)
@test F_op isa FinDomFunctor
@test getvalue(getvalue(getvalue(F_op))) isa FinDomFunctorMap
@test dom(F_op) == op(C)
@test codom(F_op) == op(Cat(D))
@test op(F_op) == F

# Composition of functors.
g, h, k = gs = path_graph.(Graph, [2,3,5])
C, D, E = FinCat.(gs)
F = FinDomFunctor([1,3], [[1,2]], C, D)
G = FinDomFunctor([1,3,5], [[1,2],[3,4]], D, E)
@test is_functorial(G)
@test hom_map(G, Path(h, [1,2])) == Path(k, [1,2,3,4])

@withmodel FinCatC() (⋅, id, codom) begin
  @test collect_ob(F⋅G) == [1,5]
  @test edges(only(collect_hom(F⋅G))) == [1,2,3,4]
  @test codom(F⋅G) == E

  @test id(C)⋅F == F
  @test F⋅id(D) == F
end

# Functors out free categories.
C = FinCat(parallel_arrows(Graph, 2))
f, g = FinFunction([1,3], 3), FinFunction([2,3], 3)
SetCat = Cat(TypeCat(SetC()))
F = FinDomFunctor([FinSet(2), FinSet(3)], [f,g], C, SetCat)
@test is_functorial(F)
@test dom(F) == C
@test codom(F) == SetCat
# @test startswith(sprint(show, F), "FinDomFunctor(")

@test ob_map(F, 1) == FinSet(2)
@test gen_map(F, 2) == g

# Commutative square as natural transformation.
C = FinCat(path_graph(Graph, 2))
F = FinDomFunctor([FinSet(4), FinSet(2)], [FinFunction([1,1,2,2])], C, SetCat)
α₀, α₁ = FinFunction([3,4,1,2]), FinFunction([2,1])


if false # TODO 
  α = FinTransformation([α₀, α₁], F, F)
  @test is_natural(α)
  @test (α[1], α[2]) == (α₀, α₁)
  @test components(α) == [α₀, α₁]
  @test α⋅α == FinTransformation([FinFunction(1:4), FinFunction(1:2)], F, F)
end

# Initial functors
##################

# Commutative square diagram: with 1→2→4 and 1→3→4
S = FinCat(@acset Graph begin
  V = 4
  E = 4
  src = [1,1,2,3]
  tgt = [2,3,4,4]
end)

# Equalizer diagram: 1→2⇉3
T = FinCat(@acset Graph begin
  V = 3
  E = 3
  src = [1,2,2]
  tgt = [2,3,3]
end)

# Extra bit added to beginning equalizer diagram: 4→1→2⇉3
T2 = FinCat(@acset Graph begin
  V = 4
  E = 4
  src = [1,2,2,4]
  tgt = [2,3,3,1]
end)

# Extra bit added to end of equalizer diagram: 1→2⇉3→4
T3 = FinCat(@acset Graph begin
  V = 4
  E = 4
  src = [1,2,2,3]
  tgt = [2,3,3,4]
end)

gen = (homtype=:generator,)
# Opposite square corners folded on top of each other
F1 = FinDomFunctor([1,2,2,3], [1,1,2,3], S, T; gen...)

# Both paths in square get mapped onto single length-2 path in equalizer
F2 = FinDomFunctor([1,2,2,3], [1,1,2,2], S, T; gen...)

# Fit equalizer into square, ignoring opposite corner
F3 = FinDomFunctor([1,2,4], [1,3,3], T, S; gen...)

# Same as F1, but there is an additional piece of data in codomain, ignored
F4 = FinDomFunctor([1,2,3], [1,2,3], T, T2; gen...)

# Same as F1, but there is an additional piece of data in codomain, ignored
F5 = FinDomFunctor([1,2,3], [1,2,3], T, T2; gen...)

@test all(is_functorial, [F1,F2,F3,F4])

@test is_initial(F1)
@test !is_initial(F2)
@test !is_initial(F3)
@test !is_initial(F4)
@test !is_initial(F5)

# Test ACSets as FinDomFunctors into Set
if false 
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
@test α_op isa FinCats.FinTransformationMap
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

end 


end # module
