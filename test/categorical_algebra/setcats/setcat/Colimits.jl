module TestSetCColimits

using Catlab, Test

const 𝒞 = SetC()

# Trivial coproduct.
####################
TC = TypeCat(𝒞)
colim = colimit[TC](SingletonDiagram(SetOb(Int)))
@test ob(colim) == SetOb(Int)

f = SetFunction(string, SetOb(Int), SetOb(String))
@test universal[TC](colim, SMulticospan{1}(f)) === f

# pushouts
###########

# f, g = FinFunction([1], 2), FinFunction([2], 3)

# colimit[𝒞](Multispan([f,g]))

# colim = pushout[𝒞](f,g)
# @test ob(colim) == FinSet(4)
# ι1, ι2 = colim

# h, k = FinDomFunction.([[:b,:c],[:a,:b,:c]], Ref(SetOb(Symbol)))

# ℓ = copair[𝒞](colim, h, k)
# @test force(compose(C,coproj1(colim), ℓ)) == h
# @test force(compose(C,coproj2(colim), ℓ)) == k
# k = FinDomFunction([:a,:d,:c], SetOb(Symbol))
# @test_throws ErrorException copair(colim,h,k)
 

end # module
