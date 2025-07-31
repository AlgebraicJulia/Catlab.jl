module TestVarACSetColimits 

using Test, Catlab

############
# LoneAttr #
############

@present SchLoneAttr(FreeSchema) begin X::AttrType end
@acset_type LoneAttr(SchLoneAttr){Bool}
const ℒ = ACSetCategory(VarACSetCat(LoneAttr()))

"""
                      g              f
                Y  <-----  X   ---->  Y 
               ---        ---        ---
               [3] <----- [1]  ----> [1]
                                     
                ⊥  <----- [2]  ---->  ⊥     
      [1] [2]                                 [2]  [4]
                ⊤  <----- [3]  ----> [3]
                                   
               [4] <----- [4]  ---->  [4]
"""
X = @acset LoneAttr begin X = 4 end
Y = @acset LoneAttr begin X = 4 end
f = ACSetTransformation(X, Y; X=[AttrVar(1), false, AttrVar(3), AttrVar(4)])
g = ACSetTransformation(X, Y; X=[AttrVar(3), false, true, AttrVar(4)])

"""
Coequalization merges [1] and [3] and ⊥ as well as [4] and ⊤ 

Y: [1]  [3]  [2]  [4]
    ↘  ↙      ↓    ↓
Q:   ⊤       [1]  [2]       <-- these variables represent eq classes 
                                 of variables in Y
"""

π, = coeq = coequalizer[ℒ](f,g)
@test get(π[:X]) ≃ FinDomFunction([Right(true), Left(1), Right(true), Left(2)], either(FinSet(2), SetOb(Bool)))

A = @acset LoneAttr begin X = 3 end

XA = ACSetTransformation(X, A; X=[true, true, false, AttrVar(3)])

factorize[ℒ](coeq, XA)
@test get(factorize[ℒ](coeq, XA)[:X]) |> collect == [Right(true), Left(3)]

####################
# VE-labeled Graph #
####################

@present SchVELabeledGraph <: SchGraph begin
  Label::AttrType; vlabel::Attr(V,Label); elabel::Attr(E,Label)
end

@acset_type VELabeledGraph(SchVELabeledGraph,index=[:src,:tgt]) <: AbstractGraph

const VES = VELabeledGraph{Symbol}

const 𝒱 = ACSetCategory(VarACSetCat(VES()))

# Coproduct
###########

g = @acset VES begin
  V=2; E=2; Label=2; src=1; tgt=2; 
  vlabel=[AttrVar(1),:b]; elabel=[:e, AttrVar(2)] 
end

expected = @acset VES begin 
  V=4; E=4; Label=4; src=[1,1,3,3]; tgt=[2,2,4,4]
  vlabel=[AttrVar(1),:b,AttrVar(3),:b]; 
  elabel=[:e,AttrVar(2),:e,AttrVar(4)] 
end

colim = ι₁, ι₂ = coproduct[𝒱](g, g);

@test ob(colim) == expected
@test ι₁[:V](1) == 1
@test ι₂[:V](1) == 3
@test collect(get(ι₁[:Label])) == Left.(1:2)
@test collect(get(ι₂[:Label])) == Left.(3:4)


# Coequalizers
##############

I = @acset VES begin V=2; E=1; Label=1
  src=1; tgt=2; vlabel=[:x,:x]; elabel=[AttrVar(1)]
end
VX = @acset VES begin V=1; vlabel=[:x] end
# Coequalizer in Graph: collapsing a segment to a loop.
VES(1)#; V=(vlabel=[:x],))
α = ACSetTransformation((V=[1], E=Int[]), VX, I; cat=𝒱)
β = ACSetTransformation((V=[2], E=Int[]), VX, I; cat=𝒱)
@test is_natural(α, cat=𝒱) && is_natural(β, cat=𝒱)
coeq = coequalizer[𝒱](α, β)

expected = @acset VES begin V=1; E=1; Label=1
  src=1; tgt=1; vlabel=[:x]; elabel=[AttrVar(1)]
end
@test ob(coeq) == expected
@test force(proj(coeq)[:V]) == FinFunction([1,1])
@test force(proj(coeq)[:E]) == FinFunction([1])
@test get(proj(coeq)[:Label]) ≃ pure(FinFunction([1]), Symbol)


# Pushouts
###########
g1 = @acset VES begin V=2; E=1; Label=2
  src=1; tgt=2; vlabel=[:x,AttrVar(2)]; elabel=[AttrVar(1)]
end
g2 = @acset VES begin V=1; E=1; Label=1
  src=1; tgt=1; vlabel=[:x]; elabel=[AttrVar(1)]
end

α = ACSetTransformation((V=[1], E=Int[]), VX, g1; cat=𝒱)
β = ACSetTransformation((V=[1], E=Int[]), VX, g2; cat=𝒱)
@test is_natural(α; cat=𝒱) && is_natural(β; cat=𝒱)
colim = pushout[𝒱](α, β);
@test nv(ob(colim)) == 2
@test src(ob(colim)) == [1,1]
@test tgt(ob(colim)) == [2,1]
@test is_natural(coproj1(colim); cat=𝒱) && is_natural(coproj2(colim); cat=𝒱)

#################
# WeightedGraph #
#################

const WG = WeightedGraph{Bool}

const 𝒞 = ACSetCategory(VarACSetCat(WG()))

A = @acset WG begin
  V=1; E=2; Weight=2; src=1; tgt=1; weight=[AttrVar(1),true] 
end

# Initial object 
################

i = initial[𝒞]()

@test dom(create[𝒞](A)) == WG()

# COPRODUCT
###########
AA = coproduct[𝒞](A,A)
@test apex(AA)[:weight] == [AttrVar(1),true,AttrVar(3),true]
ι₂w = get(legs(AA)[2][:Weight])
@test ι₂w.(1:2) == Left.(3:4) # attrvar mapping

X = @acset WG begin V=1;E=1;Weight=2;src=1;tgt=1;weight=[true] end
f′ = homomorphism(A, X; initial=(Weight=[true,AttrVar(1)],), cat=𝒞)
g′ = homomorphism(A, X; initial=(Weight=[true,AttrVar(2)],), cat=𝒞)

fg = copair[𝒞](AA, f′,g′)
@test is_natural(fg; cat=𝒞)
@test collect(get(fg[:Weight])) == [Right(true), Left(1), Right(true), Left(2)]

# PUSHOUTS
##########

V = @acset WG begin Weight=1 end
f = ACSetTransformation(Dict(:Weight=>[AttrVar(1)]), V, A)
g = ACSetTransformation(Dict(:Weight=>[AttrVar(2)]), V, A)

ι₁,ι₂ = clim = colimit[𝒞](Span(f,g));
@test is_natural(ι₁; cat=𝒞)
@test is_natural(ι₂; cat=𝒞)
@test collect(get(ι₂[:Weight])) == Left.([3,1])

f′ = homomorphism(A, X; initial=(Weight=[true,AttrVar(2)],), cat=𝒞)
g′ = homomorphism(A, X; initial=(Weight=[true,true],), cat=𝒞)
fg = universal[𝒞](clim, Cospan(f′,g′))

@test collect(get(fg[:Weight])) == [Right(true), Left(2), Right(true)]

end # module
