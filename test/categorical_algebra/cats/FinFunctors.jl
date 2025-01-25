module TestFinFunctors 

using Catlab, Test

# Functors between free categories.
h = @acset Graph begin V=4; E=4; src=[1,1,2,3]; tgt= [2,3,4,4] end
D = FinCat(h)

C = FinCat(parallel_arrows(Graph, 2))
F = FinFunctor((V=[1,4], E=[[1,3], [2,4]]), C, D)
G = FinFunctor((V=[2,1], E=[[1],[2]]), C, C)
@test dom(F) == C
@test codom(F) == D
@test is_functorial(F)
@test !is_functorial(G)
@test map(collect,functoriality_failures(G)) == ([1,2],[1,2],[])
@test Ob(F) == FinFunction([1,4], FinSet(4))
@test startswith(sprint(show, F), "FinFunctor($([1,4]),")
@test ob_map(F, 2) == 4
@test hom_map(F, 1) == Path(h, [1,3])
@test collect_ob(F) == [1,4]
@test collect_hom(F) == [Path(h, [1,3]), Path(h, [2,4])]

F_op = op(F)
@test F_op isa FinFunctor && F_op isa FinDomFunctorMap
@test dom(F_op) == op(C)
@test codom(F_op) == op(D)
@test op(F_op) == F

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

end # module
