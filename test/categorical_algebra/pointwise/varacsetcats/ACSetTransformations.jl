module TestVarACSetTransformations

using Catlab, Test

const WG = WeightedGraph
A = @acset WG{Bool} begin V=1; E=2; Weight=2;
  src=1; tgt=1; weight=[AttrVar(1), true] 
end
B = @acset WG{Bool} begin V=1; E=2; Weight=1;
  src=1; tgt=1; weight=[true, false] 
end

@test VarFunction(A,:weight) == VarFunction{Bool}([AttrVar(1), true], FinSet(2))


f = ACSetTransformation(
  Dict(:V=>[1],:E=>[1,2],:Weight=>[AttrVar(2), AttrVar(1)]), A, A
)
@test !is_natural(f) # this should not be true, bug in is_natural

f = ACSetTransformation(Dict(:V=>[1],:E=>[2,1],:Weight=>[false, AttrVar(1)]), A,B)
@test is_natural(f)
@test force(id(A) ⋅ f) == force(f) == force(f ⋅ id(B))
@test f isa TightACSetTransformation
@test_throws ErrorException ACSetTransformation(
  Dict(:V=>[1],:E=>[2,1],:Weight=>[false, AttrVar(5)]), A,B)

A′ = WG(FinDomFunctor(A))
rem_part!(A,:Weight,2) #remove the dangling attrvar from A

C = FinCat(SchWeightedGraph)
obs = Dict(x=>x for x in ob_generators(C))
homs = Dict(f=> f for f in hom_generators(C))
F = FinDomFunctor(obs,homs,C,C)
A′′ = WG(compose(F,FinDomFunctor(A)))
#Test both A′ and A′′ for constructing an acset from 
# an ACSetFunctor, respectively, a FinDomFunctorMap.
@test A == A′ == A′′

end # module
