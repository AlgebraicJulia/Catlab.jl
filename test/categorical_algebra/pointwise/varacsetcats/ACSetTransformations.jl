module TestVarACSetTransformations 

using Catlab, Test

const WG = WeightedGraph{Bool}

const 𝒱 = ACSetCategory(VarACSetCat(WG()))


A = @acset WG begin V=1; E=2; Weight=2;
  src=1; tgt=1; weight=[AttrVar(1), true] 
end

B = @acset WG begin V=1; E=2; Weight=1;
  src=1; tgt=1; weight=[true, false] 
end


@test get(get_attr(𝒱, A, :weight)) == FinDomFunction(
  [Left(1), Right(true)], either(FinSet(2),SetOb(Bool)))

f = ACSetTransformation(
  Dict(:V=>[1],:E=>[1,2],:Weight=>[AttrVar(2), AttrVar(1)]), A, A; cat=𝒱
)
@test !is_natural(f)

f = ACSetTransformation(Dict(:V=>[1],:E=>[2,1],:Weight=>[false, AttrVar(1)]), A,B; cat=𝒱)
@test is_natural(f)

@withmodel 𝒱 (id, ⋅) begin 
  @test id(A) ⋅ f ≃ f 
  @test f ⋅ id(B) ≃ f 
end

@test_throws ErrorException ACSetTransformation(
  Dict(:V=>[1],:E=>[2,1],:Weight=>[false, AttrVar(5)]), A,B)

# Composition 
#------------

# TODO write tests

# Abstracting
##############
X = @acset WG begin
  V=1; E=2; Weight=1; src=1; tgt=1; weight=[AttrVar(1), true]
end
h = abstract_attributes(X)
@test nparts(dom(h), :Weight) == 2
@test codom(h) == X
@test is_natural(h)

# Mutation of codom of A->X should not modify domain
rem_part!(X, :E, 2)
@test nparts(dom(h), :E) == 2

end # module
