
# Colimits
##########

# Trivial coproduct.
colim = colimit(SingletonDiagram(TypeSet(Int)))
@test ob(colim) == TypeSet(Int)

f = SetFunction(string, TypeSet(Int), TypeSet(String))
@test universal(colim, SMulticospan{1}(f)) === f



# Pushout from a singleton set. (apply universal prop in SetC)
f, g = FinFunction([1], 2), FinFunction([2], 3)
colim = pushout(f,g)

h, k = FinDomFunction([:b,:c]), FinDomFunction([:a,:b,:c])
ℓ = copair(colim, h, k)
@test force(coproj1(colim) ⋅ ℓ) == h
@test force(coproj2(colim) ⋅ ℓ) == k
k = FinDomFunction([:a,:d,:c])
@test_throws ErrorException copair(colim,h,k)
