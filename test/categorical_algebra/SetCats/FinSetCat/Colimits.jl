module TestFinSetCatColimits 

using Catlab, Test

const 𝒞 = FinSetC()

AB = FinSet([:A,:B])
# Initial 
#########
I = initial[𝒞]()
@test ob(I) == FinSet(EmptySet())
@test collect(create[𝒞](AB)) == Symbol[]

# Coproducts
############

CP = ι₁,ι₂ = coproduct[𝒞](AB, AB)
@test ι₁(:A) == TaggedElem(:A, 1)
@test ι₂(:A) == TaggedElem(:A, 2)

sp = Cospan([FinFunction(Dict(zip(AB, x)), AB, FinSet(4)) 
             for x in [1=>2,3=>4]]...)

u = copair[𝒞](CP, sp...)
@test force(universal[𝒞](CP, sp)) == force(u)
@test u(TaggedElem(:A, 1)) == 1
@test u(TaggedElem(:B, 1)) == 2
@test u(TaggedElem(:A, 2)) == 3
@test u(TaggedElem(:B, 2)) == 4

end # module