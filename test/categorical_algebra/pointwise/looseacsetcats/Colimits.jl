module TestLooseACSetColimits

using Catlab, Test

@present SchSetAttr(FreeSchema) begin
  X::Ob; D::AttrType; f::Attr(X,D)
end
@acset_type SetAttr(SchSetAttr)

# Pushout with given type components.
A = @acset SetAttr{Symbol} begin X=2; f=[:a,:b] end
B = @acset SetAttr{Symbol} begin X=2; f=[:x,:y] end
C = @acset SetAttr{Symbol} begin X=1; f=[:z] end
β = LooseACSetTransformation((X=[1,2],), (D=FinFunction(Dict(:a=>:x,:b=>:y)),), A, B)
γ = LooseACSetTransformation((X=[1,1],), (D=FinFunction(Dict(:a=>:z,:b=>:z)),), A, C)
@test all(is_natural, (β,γ))
g = (D=FinFunction(Dict(:x=>:q, :y=>:q)),)
h = (D=FinFunction(Dict(:z=>:q)),)
colim = pushout(β, γ, type_components=[g,h])
@test all(is_natural, legs(colim))
@test ob(colim) == @acset(SetAttr{Symbol}, begin X=1; f=[:q] end)
h′ = (D=FinFunction(Dict(:z=>:b)),)
@test_throws ErrorException pushout(β, γ, type_components=[g,h′])

end # module
