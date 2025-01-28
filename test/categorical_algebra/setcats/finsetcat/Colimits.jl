module TestFinSetCatColimits 

using Catlab, Test

const 𝒞 = FinSetC()

AB = FinSet([:A,:B])
ABC = FinSet([:A,:B,:C])
WXYZ = FinSet([:W,:X,:Y,:Z])

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


################
# Coequalizers #
################

# Coequalizer from a singleton set.
#----------------------------------
f, g = FinFunction.([Dict(:x=>x) for x in [:A,:C]], Ref(FinSet(Set([:x]))), Ref(ABC))
coeq = coequalizer[𝒞](f,g)
@test proj(coeq) == FinFunction(Dict(:A=>:A,:B=>:B,:C=>:A), ABC, AB)
@test factorize[𝒞](coeq, FinFunction(Dict(:A=>:Z,:B=>:W,:C=>:Z), ABC, WXYZ)
  ) == FinFunction(Dict(:A=>:Z,:B=>:W), AB, WXYZ)

# Coequalizer in case of identical functions.
#--------------------------------------------
f = FinFunction(Dict(:W=>4,:X=>2,:Y=>3,:Z=>1),WXYZ, FinSet(5))
coeq = coequalizer[𝒞](f,f)
@test all(proj(coeq)(i) == i for i in 1:5)
  
fact = factorize[𝒞](coeq, FinFunction([2,1,3,3,4],4))
exp = FinFunction([2,1,3,3,4],4)
@test all(1:5) do i 
  fact(i) == exp(i)
end

# Coequalizer identifying everything.
#-------------------------------------
f, g = id[𝒞](ABC), FinFunction(Dict(:A=>:B,:B=>:C,:C=>:A), ABC, ABC)
coeq = coequalizer[𝒞](f,g)
@test all(i -> proj(coeq)(i) == :A, ABC)

fact = factorize[𝒞](coeq, FinFunction(Dict(:A=>1,:B=>1,:C=>1), ABC, FinSet(3)))
@test fact(:A) == 1

############
# Pushouts #
############

const 𝕀 = FinSet(nothing)

# Pushout from the empty set: the degenerate case of the coproduct.
#-----------------------------------------------------------------
f, g = FinFunction(Symbol[], AB), FinFunction(Nothing[], 𝕀)
colim = pushout[𝒞](f,g)

a1, b1, n = TaggedElem.([:A,:B,nothing],[1,1,2])
@test ob(colim) == FinSet([a1,b1,n])

@test force(coproj1(colim)) == FinFunction(
  Dict(:A=>a1,:B=>b1), AB, ob(colim))

@test force(coproj2(colim)) == FinFunction(
  Dict(nothing=>n), 𝕀, ob(colim))

h, k = FinFunction.([Dict(:A=>3,:B=>5), Dict(nothing=>4)], [AB,𝕀], Ref(FinSet(5)))
ℓ = copair[𝒞](colim, h, k)

@test ℓ.([a1, b1, n]) == [3,5,4]

@withmodel 𝒞 (⋅) begin
  @test force(coproj1(colim) ⋅ ℓ) == h
  @test force(coproj2(colim) ⋅ ℓ) == k
end

# Pushout from a singleton set.
#------------------------------
f = FinFunction(Dict(nothing=>1), 𝕀, FinSet(2))
g = FinFunction(Dict(nothing=>2), 𝕀, FinSet(3))
colim = ι1, ι2 = pushout[𝒞](f,g)

x11,x21,x12,x32 = TaggedElem.([1,2,1,3],[1,1,2,2])
@test ob(colim) == FinSet([x11,x21,x12,x32])

@withmodel 𝒞 (⋅) begin
  @test force(f⋅ι1) == force(g⋅ι2)
  @test force(ι1) == FinFunction([x11,x21], ob(colim))
  @test force(ι2) == FinFunction([x12,x11,x32], ob(colim))
end 

h, k = FinFunction([:A,:B], ABC), FinFunction([:C,:A,:B], ABC)

ℓ = pushout_copair[𝒞](colim, h, k)

@withmodel 𝒞 (⋅) begin
  @test force(coproj1(colim) ⋅ ℓ) == h
  @test force(coproj2(colim) ⋅ ℓ) == k
end


# Pushout with names.
#---------------------
A, B = FinSet.(Set.([[:w, :x, :y1],[:x, :y2, :z]]))
f, g = FinFunction(Dict(:y => :y1), A), FinFunction(Dict(:y => :y2), B)
colim = ι1, ι2 = pushout[𝒞](f, g)
X = ob(colim)
@test Set(X) == Set(TaggedElem.([:w,:x,:x,:y1,:z], [1,1,2,1,2]))

@test force(ι1).val.val == Dict(x => TaggedElem(x, 1) for x in A) 
@test force(ι2).val.val == Dict(
  x => x == :y2 ? TaggedElem(:y1, 1) : TaggedElem(x, 2) for x in B) 

end # module
