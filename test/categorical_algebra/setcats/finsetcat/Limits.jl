module TestFinSetCatLimits 

using Catlab, Test

const 𝒞 = FinSetC()

AB = FinSet([:a,:b])

# Terminal object.
##################
T = limit[𝒞](EmptyDiagram{FinSet}())
@test ob(T) == FinSet(nothing)
@test delete[𝒞](AB)(:a) === nothing

# Singleton limit
#################
TC = TypeCat(𝒞)
lim = limit[TC](SingletonDiagram(AB))
@test ob(lim) == AB
f = FinFunction(Dict(:a=>1,:b=>:2), AB, FinSet(2))
@test universal[TC](lim, Multispan([f])) === f

# Product
#########

P = ProdSet([AB,AB])

lim = π₁,π₂ = product[𝒞](AB,AB)

@test π₁((:a,:b)) == π₂((:b,:a)) == :a
sp = Span(FinFunction.(FinFunctionVector.([[:a,:b,:b],[:a,:b,:a]], Ref(AB)))...)  
u = pair[𝒞](lim, sp...)
@test collect(u) == [(:a,:a),(:b,:b),(:b,:a)]
@test force(universal[𝒞](lim, sp)) == force(u)

# Equalizer
###########

f = FinFunction([2,1,3],4)
g = FinFunction([1,2,3],4)
eq1 = equalizer[𝒞](f,g)
e = dom(only(eq1))
@test collect(e) == [3]
@test only(eq1)(3) == 3

h = FinFunction([3,3],4)
@test factorize[𝒞](eq1, h) == FinFunction([1,1])

end # module
