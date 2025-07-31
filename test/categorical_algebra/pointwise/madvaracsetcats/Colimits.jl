module TestMADVarACSetColimits 

using Test, Catlab

cat = ACSetCategory(WeightedGraph{Symbol}());
G2 = @acset WeightedGraph{Symbol} begin 
  V=2; E=2; src=[1,2]; tgt=[1,2]; weight=[:X, :Y] 
end
clim = coproduct[cat](G2,G2);
universal[cat](clim, Cospan(id[cat](G2), id[cat](G2)))

############
# LoneAttr #
############

@present SchLoneAttr(FreeSchema) begin X::AttrType end
@acset_type LoneAttr(SchLoneAttr, part_type=BitSetParts){Bool}
const ℒ = ACSetCategory(MADVarACSetCat(LoneAttr()))

X = @acset LoneAttr begin X = 4 end
Y = @acset LoneAttr begin X = 4 end

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
f = ACSetTransformation(X, Y; 
                        X=[AttrVar(1), false, AttrVar(3), AttrVar(4)], cat=ℒ)
g = ACSetTransformation(X, Y; 
                        X=[AttrVar(3), false, true, AttrVar(4)], cat=ℒ)

"""
Coequalization merges [1] and [3] and ⊥ as well as [4] and ⊤ 

Y: [1]  [3]  [2]  [4]
    ↘  ↙      ↓    ↓
Q:   ⊤       [1]  [2]       <-- these variables represent eq classes 
                                 of variables in Y
"""
q, = coeq = coequalizer[ℒ](f,g);

A = @acset LoneAttr begin X = 3 end

"""
Y: [1] [2] [3] [4]
    ↓   ↓   ↓   ↓
A:  ⊥   ⊤   ⊥  [3]  [1]  [2]
"""
YA = ACSetTransformation(Y, A; X=[true, true, false, AttrVar(3)], cat=ℒ)

"""
So a map out of Y which sends {1,3} to ⊥, {2} to ⊤, and {4} to {3}
can be transported to a map out of the equivalence classes:
"""

@test factorize[ℒ](coeq, YA)[:X].val.val.val == Dict(1=> Right(true), 2=>Left(3))

####################
# VE-labeled Graph #
####################

@present SchVELabeledGraph <: SchGraph begin
  Label::AttrType; vlabel::Attr(V,Label); elabel::Attr(E,Label)
end

@acset_type VELabeledGraph(SchVELabeledGraph,index=[:src,:tgt],part_type=BitSetParts) <: AbstractGraph

const VES = VELabeledGraph{Symbol}

const 𝒱 = ACSetCategory(MADVarACSetCat(VES()))

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

colim = ι₁, ι₂ = coproduct[𝒱](g, g)

@test is_isomorphic(ob(colim), expected)
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
@test is_natural(α, cat=𝒱)
@test is_natural(β, cat=𝒱)
prj, = coeq = coequalizer[𝒱](α, β)

expected = @acset VES begin V=1; E=1; Label=1
  src=1; tgt=1; vlabel=[:x]; elabel=[AttrVar(1)]
end
@test ob(coeq) == expected
@test force(prj[:V]) ≃ FinFunction(Dict(1=>1,2=>1))
@test force(prj[:E]) ≃ FinFunction(Dict(1=>1))
@test Dict(get(prj[:Label])) == Dict(pure(FinFunction(Dict(1=>1)), Symbol))

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
@test is_natural(α; cat=𝒱) 
@test is_natural(β; cat=𝒱)
colim = pushout[𝒱](α, β);
@test nv(ob(colim)) == 2
@test src(ob(colim)) == [2,2]
@test tgt(ob(colim)) == [1,2]
@test is_natural(coproj1(colim); cat=𝒱)
@test is_natural(coproj2(colim); cat=𝒱)

#################
# WeightedGraph #
#################

@acset_type WG(SchWeightedGraph, part_type=BitSetParts){Bool} <: AbstractGraph
const 𝒞 = ACSetCategory(MADVarACSetCat(WG()))


"""
A graph with two loops:      ⊤↻•↺[1]       [2]
and an unbound Weight attrvar
"""
A = @acset WG begin 
  V=1; E=2; Weight=2; src=1; tgt=1; weight=[AttrVar(1),true] 
end

# Initial object 
################

i = initial[𝒞]()

@test dom(create[𝒞](A)) == WG()


B = @acset WG begin 
  V=1; E=1; Weight=1; src=1; tgt=1; weight=[AttrVar(1)] 
end
@test dom(create[𝒞](B)) == WG()


# COPRODUCT
###########

"""
A graph with two copies of two loops:      ⊤↻•↺[2]   ⊤↻•↺[4]     [1]  [3]
and two unbound Weight attrvars
"""
expected = @acset WG begin 
  V=2; E=4; Weight=4; src=[1,1,2,2]; tgt=[1,1,2,2]; 
  weight=[true,AttrVar(2), true, AttrVar(4)]
end

ι₁,ι₂ = AA = coproduct[𝒞](A,A);

@test is_isomorphic(ob(AA), expected)


"""
Two maps from A+A to a graph X:  ⊤↻•   [1]  [2]
These only have one choice for their vertex and edge and first weight variable, however they have freedom over their second weight variable.
f sends it to [1], g sends it to [2]
"""
X = @acset WG begin V=1;E=1;Weight=2;src=1;tgt=1;weight=[true] end
f′ = homomorphism(A, X; initial=(Weight=[true,AttrVar(1)],), cat=𝒞)
g′ = homomorphism(A, X; initial=(Weight=[true,AttrVar(2)],), cat=𝒞)

""" Thus copairing f and g takes these two maps A -> X 
and gives one map A + A -> X
"""
fg = copair[𝒞](AA, f′, g′);
@test is_natural(fg; cat=𝒞)
@test force(compose[𝒞](ι₁, fg); cat=𝒞) == force(f′; cat=𝒞)
@test force(compose[𝒞](ι₂, fg); cat=𝒞) == force(g′; cat=𝒞)

# PUSHOUTS
##########

""" A has two loops, and two variables (one floating, one on a loop) 

We can merge the two variables into one by coequalizing a map that picks out just the loop variable and another that picks out the free variable
"""
V = @acset WG begin Weight=1 end
f = ACSetTransformation(Dict(:Weight=>[AttrVar(1)]), V, A, cat=𝒞)
g = ACSetTransformation(Dict(:Weight=>[AttrVar(2)]), V, A, cat=𝒞)

q, = coeq = coequalizer[𝒞](f, g);

@test get(q[:Weight]).(1:2) == [Left(1), Left(1)]
@test nparts(ob(coeq), :Weight) == 1


""" If we just coproducted A, we'd get two pairs of loops and two 
floating variables. But by pushing out with the above maps we merge the free variable from one of the copies of A with the loop variable of the other """
ι₁,ι₂ = clim = colimit[𝒞](Span(f,g));

@test nparts(ob(clim), :Weight) == 3


@test is_natural(ι₁;  cat=𝒞)
@test is_natural(ι₂; cat=𝒞)

f′ = homomorphism(A, X; initial=(Weight=[true,AttrVar(2)],), cat=𝒞)
g′ = homomorphism(A, X; initial=(Weight=[true,true],), cat=𝒞)
# fg = universal[𝒞](clim, Cospan(f′,g′; cat=𝒞)) # NOT YET WORKING

# @test collect(fg[:Weight]) == [Right(true), Left(2), Right(true)]

end # module
