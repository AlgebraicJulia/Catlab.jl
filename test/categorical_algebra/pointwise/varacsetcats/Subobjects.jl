module TestVarSubobjects

using Catlab, Test 

@present SchSetAttr(FreeSchema) begin
  X::Ob
  D::AttrType
  f::Attr(X,D)
end
@acset_type SetAttr(SchSetAttr)

X = @acset SetAttr{Bool} begin X=2;D=1;f=[true, AttrVar(1)] end
A = Subobject(X, X=[1])
B = Subobject(X, X=[2], D=[1])
@test A ∧ B |> force == ⊥(X) |> force
@test A ∨ B |> force == ⊤(X) |> force


@present SchVELabeledGraph <: SchGraph begin
  Label::AttrType; vlabel::Attr(V,Label); elabel::Attr(E,Label)
end

@acset_type VELabeledGraph(SchVELabeledGraph,
                           index=[:src,:tgt]) <: AbstractGraph

const VES = VELabeledGraph{Symbol}

"""
  e1    e4 
a ↘  e3  ↗ e        A = [a,b,c,d] + [1,2,3]
   c → d 
b ↗     ↘ f         B = [c,d,e,f] + [3,4,5]
  e2   e5
"""
X = @acset VES begin V=6; E=5; Label=5
  src=[1,2,3,4,4]; tgt=[3,3,4,5,6];
  vlabel=[:a,:b,:c,:d,:e,:f]; elabel=AttrVar.(1:5)
end

A′ = Subobject(X, V=1:4, E=1:3, Label=1:3) # component-wise representation
B′ = Subobject(X, V=3:6, E=3:5, Label=3:5)
A′′, B′′ = Subobject.(hom.([A′,B′])) # hom representation

for (A,B) in [A′=>B′, A′′ =>B′′]
  @test A ∧ B |> force == Subobject(X, V=3:4, E=3:3, Label=3:3) |> force
  expected = @acset VES begin V=2; E=1; Label=1;
    src=1; tgt=2; vlabel=[:c,:d]; elabel=[AttrVar(1)]
  end
  @test is_isomorphic(dom(hom(A ∧ B )), expected)
  @test A ∨ B |> force == Subobject(X, V=1:6, E=1:5, Label=1:5) |> force
  @test ⊤(X) |> force == A ∨ B |> force
  @test ⊥(X) |> force == Subobject(X, V=1:0, E=1:0, Label=1:0) |> force
  @test force(implies(A, B)) == force(¬(A) ∨ B)
  @test ¬(A ∧ B) == ¬(A) ∨ ¬(B)
  @test ¬(A ∧ B) != ¬(A) ∨ B
  @test (A ∧ implies(A,B)) == B ∧ (A ∧ implies(A,B))
  @test (B ∧ implies(B,A)) == A ∧ (B ∧ implies(B,A))
  @test ¬(A ∨ (¬B)) == ¬(A) ∧ ¬(¬(B))
  @test ¬(A ∨ (¬B)) == ¬(A) ∧ B
  @test A ∧ ¬(¬(A)) == ¬(¬(A))
  @test implies((A∧B), A) == A∨B
  @test dom(hom(subtract(A,B))) == @acset VES begin V=3; E=2; Label=2
    src=[1,2]; tgt=3; vlabel=[:a,:b,:c]; elabel=AttrVar.(1:2)
  end

  @test nv(dom(hom(~A))) == 3
end

end # module
