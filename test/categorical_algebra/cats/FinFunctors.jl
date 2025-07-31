module TestFinFunctors 

using Test, Catlab, ACSets

using .ThCategory

# Preorder cats
###############
po1 = PreorderFinCat([(:a,:b)]) |> FinCat
po2 = PreorderFinCat([(1,2),(2,3)]) |> FinCat

F = FinFunctor(Dict(:a=>1,:b=>2),
  Dict(x=>x for x in hom_generators(po1)), po1, po2; homtype=:hom)

@test id(po1, :a) == (1=>1)

@test hom_map(F, 1=>1) == (1=>1)
  

h = @acset Graph begin V=4; E=4; src=[1,1,2,3]; tgt= [2,3,4,4] end
D = FinCat(h)

# Functors between free categories.

C = FinCat(parallel_arrows(Graph, 2))
F = FinFunctor((V=[1,4], E=[[1,3], [2,4]]), C, D; homtype=:list)
G = FinFunctor((V=[2,1], E=[1,2]), C, C; homtype=:generator)
@test dom(F) == C
@test codom(F) == D
@test is_functorial(F)
@test !is_functorial(G)
@test map(collect,functoriality_failures(G)) == ([1,2],[1,2],[])
# @test startswith(sprint(show, F), "FinFunctor($([1,4]),")
@test ob_map(F, 2) == 4
@test gen_map(F, 1) == Path(h, [1,3])
@test collect_ob(F) == [1,4]
@test collect_hom(F) == [Path(h, [1,3]), Path(h, [2,4])]

F_op = op(F)
@test F_op isa FinFunctor
@test getvalue(getvalue(getvalue(F_op))) isa FinDomFunctorMap
@test dom(F_op) == op(C)
@test codom(F_op) == op(D)
@test op(F_op) == F

# Composition of functors.
g, h, k = gs = path_graph.(Graph, [2,3,5])
C, D, E = FinCat.(gs)
F = FinFunctor([1,3], [[1,2]], C, D; homtype=:list) |> force
G = FinFunctor([1,3,5], [[1,2],[3,4]], D, E; homtype=:list)
@test is_functorial(G)
@test hom_map(G, Path(h, [1,2])) == Path(k, [1,2,3,4])

@withmodel FinCatC() (⋅, id, codom) begin
  @test collect_ob(F⋅G) == [1,5]
  @test edges(only(collect_hom(F⋅G))) == [1,2,3,4]
  @test codom(F⋅G) == E

  @test force(id(C)⋅F) == F
  @test force(F⋅id(D)) == F
end

# Functors out free categories.
C = FinCat(parallel_arrows(Graph, 2))
f, g = FinFunction([1,3], 3), FinFunction([2,3], 3)
𝒞 = Cat(TypeCat(SetC()))
F = FinDomFunctor(SetOb.(FinSet.(2:3)), SetFunction.([f,g]), C, 𝒞)
@test is_functorial(F)
@test dom(F) == C
@test codom(F) == 𝒞
# @test startswith(sprint(show, F), "FinDomFunctor(")

@test ob_map(F, 1) == SetOb(FinSet(2))
@test gen_map(F, 2) == SetFunction(g)


# Initial functors
##################

# Commutative square diagram: with 1→2→4 and 1→3→4
S = FinCat(@acset Graph begin
  V = 4; E = 4; src = [1,1,2,3]; tgt = [2,3,4,4]
end)

# Equalizer diagram: 1→2⇉3
T = FinCat(@acset Graph begin
  V = 3; E = 3; src = [1,2,2]; tgt = [2,3,3]
end)

# Extra bit added to beginning equalizer diagram: 4→1→2⇉3
T2 = FinCat(@acset Graph begin
  V = 4; E = 4; src = [1,2,2,4]; tgt = [2,3,3,1]
end)

# Extra bit added to end of equalizer diagram: 1→2⇉3→4
T3 = FinCat(@acset Graph begin
  V = 4; E = 4; src = [1,2,2,3]; tgt = [2,3,3,4]
end)

gen = (homtype=:generator,)
# Opposite square corners folded on top of each other
F1 = FinFunctor([1,2,2,3], [1,1,2,3], S, T; gen...)

# Both paths in square get mapped onto single length-2 path in equalizer
F2 = FinFunctor([1,2,2,3], [1,1,2,2], S, T; gen...)

# Fit equalizer into square, ignoring opposite corner
F3 = FinFunctor([1,2,4], [1,3,3], T, S; gen...)

# Same as F1, but there is an additional piece of data in codomain, ignored
F4 = FinFunctor([1,2,3], [1,2,3], T, T2; gen...)

# Same as F1, but there is an additional piece of data in codomain, ignored
F5 = FinFunctor([1,2,3], [1,2,3], T, T2; gen...)

@test all(is_functorial, [F1,F2,F3,F4])

@test is_initial(F1)
@test !is_initial(F2)
@test !is_initial(F3)
@test !is_initial(F4)
@test !is_initial(F5)

# Test ACSets as FinDomFunctors into Set
V, E, src′, tgt′ = generators(SchGraph)
# Graph as set-valued functor on a free category.
acs = path_graph(Graph, 3)
FinDomFunctor(ACSetFunctor(acs,infer_acset_cat(acs)))

F = FinDomFunctor(path_graph(Graph, 3))
𝒞 = dom(F)
@test 𝒞 == FinCat(SchGraph)
@test is_functorial(F)
@test ob_map(F, V) == FinSetInt(3)
@test ob_map(F, E) == FinSetInt(2)
@test hom_map(F, src′) == FinFunction([1,2], 3)
@test hom_map(F, tgt′) == FinFunction([2,3], 3)
@test hom_map(F, id(E)) == id[FinSetC()](FinSet(2))

end # module
