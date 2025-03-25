using Catlab, Test 

# Initial object.
@test ob(initial(FinSet{Int})) == FinSet(0)
@test create(initial(FinSet{Int}), FinSet(3)) == FinFunction(Int[], 3)

# Binary coproduct.
colim = coproduct(FinSet(2), FinSet(3))
@test ob(colim) == FinSet(5)
@test coproj1(colim) == FinFunction([1,2], 5)
@test coproj2(colim) == FinFunction([3,4,5], 5)

f, g = FinFunction([3,5], 5), FinFunction([1,2,3], 5)
h = copair(colim, f, g)
@test force(coproj1(colim) ⋅ h) == f
@test force(coproj2(colim) ⋅ h) == g

# N-ary coproduct.
colim = coproduct([FinSet(2), FinSet(3)])
@test ob(colim) == FinSet(5)
@test legs(colim) == [FinFunction([1,2], 5), FinFunction([3,4,5], 5)]
@test ob(coproduct(FinSet{Int}[])) == FinSet(0)

h = copair(colim, [f,g])
@test force(first(legs(colim)) ⋅ h) == f
@test force(last(legs(colim)) ⋅ h) == g

# Cocartesian monoidal structure.
@test FinSet(2)⊕FinSet(3) == FinSet(5)
@test oplus([FinSet(2), FinSet(3), FinSet(4)]) == FinSet(9)
@test f⊕g == FinFunction([3,5,6,7,8], 10)
@test mzero(FinSet{Int}) == FinSet(0)
@test swap(FinSet(2), FinSet(3)) == FinFunction([4,5,1,2,3])
ι1, ι2 = coproj1(FinSet(2),FinSet(3)), coproj2(FinSet(2),FinSet(3))
@test ι1 == FinFunction([1,2], 5)
@test ι2 == FinFunction([3,4,5], 5)

# Coequalizers
#-------------

# Coequalizer from a singleton set.
f, g = FinFunction([1], 3), FinFunction([3], 3)
coeq = coequalizer(f,g)
@test proj(coeq) == FinFunction([1,2,1], 2)
@test proj(coequalizer([f,g])) == proj(coeq)
@test factorize(coeq, FinFunction([4,1,4])) == FinFunction([4,1])
@test_throws ErrorException factorize(coeq, FinFunction([3,1,4]))

# Coequalizer in case of identical functions.
f = FinFunction([4,2,3,1], 5)
coeq = coequalizer(f,f)
@test proj(coeq) == force(id(FinSet(5)))
@test proj(coequalizer([f,f])) == proj(coeq)
@test factorize(coeq, FinFunction([2,1,3,3,4])) == FinFunction([2,1,3,3,4])

# Coequalizer identifying everything.
f, g = id(FinSet(5)), FinFunction([2,3,4,5,1], 5)
coeq = coequalizer(f,g)
@test proj(coeq) == FinFunction(fill(1,5))
@test proj(coequalizer([f,g])) == proj(coeq)
@test factorize(coeq, FinFunction(fill(3,5))) == FinFunction([3])

# Pushouts
#---------

# Pushout from the empty set: the degenerate case of the coproduct.
f, g = FinFunction(Int[], 2), FinFunction(Int[], 3)
colim = pushout(f,g)
@test ob(colim) == FinSet(5)
@test coproj1(colim) == FinFunction([1,2], 5)
@test coproj2(colim) == FinFunction([3,4,5], 5)

h, k = FinFunction([3,5], 5), FinFunction([1,2,3], 5)
ℓ = copair(colim, h, k)
@test force(coproj1(colim) ⋅ ℓ) == h
@test force(coproj2(colim) ⋅ ℓ) == k

# Pushout from a singleton set.
f, g = FinFunction([1], 2), FinFunction([2], 3)
colim = pushout(f,g)
@test ob(colim) == FinSet(4)
ι1, ι2 = colim
@test compose(f,ι1) == compose(g,ι2)
@test ι1 == FinFunction([1,2], 4)
@test ι2 == FinFunction([3,1,4], 4)

h, k = FinFunction([3,5]), FinFunction([1,3,5])
ℓ = copair(colim, h, k)
@test force(coproj1(colim) ⋅ ℓ) == h
@test force(coproj2(colim) ⋅ ℓ) == k
k = FinFunction([1,2,5])
@test_throws ErrorException copair(colim,h,k)


# Same thing as a colimit of a general free diagram.
diagram = FreeDiagram([FinSet(1),FinSet(2),FinSet(3)],[(f,1,2), (g,1,3)])
colim = colimit(diagram)
@test ob(colim) == FinSet(4)
_, ι1, ι2 = colim
@test compose(f,ι1) == compose(g,ι2)
@test ι1 == FinFunction([1,2], 4)
@test ι2 == FinFunction([3,1,4], 4)

h, k = FinFunction([3,5]), FinFunction([1,3,5])
ℓ = universal(colim, Multicospan([f⋅h, h, k])) # f⋅h == g⋅k
@test force(ι1 ⋅ ℓ) == h
@test force(ι2 ⋅ ℓ) == k

# Pushout from a two-element set, with non-injective legs.
f, g = FinFunction([1,1], 2), FinFunction([1,2], 3)
colim = pushout(f,g)
@test ob(colim) == FinSet(3)
ι1, ι2 = colim
@test compose(f,ι1) == compose(g,ι2)
@test ι1 == FinFunction([1,2], 3)
@test ι2 == FinFunction([1,1,3], 3)

# Same thing as a colimit of a general free diagram.
diagram = FreeDiagram([FinSet(2),FinSet(2),FinSet(3)],[(f,1,2),(g,1,3)])
colim = colimit(diagram)
@test ob(colim) == FinSet(3)
_, ι1, ι2 = colim
@test ι1 == FinFunction([1,2], 3)
@test ι2 == FinFunction([1,1,3], 3)

# Same thing as a colimit of a bipartite free diagram.
bdiagram = BipartiteFreeDiagram([FinSet(2)], [FinSet(2),FinSet(3)],
                                [(f,1,1),(g,1,2)])
colim = colimit(bdiagram)
@test ob(colim) == FinSet(3)
ι1, ι2 = colim
@test ι1 == FinFunction([1,2], 3)
@test ι2 == FinFunction([1,1,3], 3)
colim′ = colimit(diagram, ToBipartiteColimit())
@test legs(colim′)[2:3] == legs(colim)