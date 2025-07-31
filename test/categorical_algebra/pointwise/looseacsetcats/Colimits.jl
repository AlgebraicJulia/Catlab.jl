module TestLooseACSetColimits 

using Catlab, Test

# Pushout with given type components.
@present SchSetAttr(FreeSchema) begin
  X::Ob; D::AttrType; f::Attr(X,D)
end
@acset_type SetAttr(SchSetAttr)
const Sym = SetAttr{Symbol}
cat = ACSetCategory(LooseACSetCat(Sym()))


A = @acset SetAttr{Symbol} begin X=2; f=[:a,:b] end
B = @acset SetAttr{Symbol} begin X=2; f=[:x,:y] end
C = @acset SetAttr{Symbol} begin X=1; f=[:z] end
β = ACSetTransformation((X=[1,2],D=FinFunction(Dict(:a=>:x,:b=>:y)),), A, B; cat)
γ = ACSetTransformation((X=[1,1],D=FinFunction(Dict(:a=>:z,:b=>:z)),), A, C; cat)
@test all(is_natural, (β,γ))
g = (D=FinFunction(Dict(:x=>:q, :y=>:q)),)
h = (D=FinFunction(Dict(:z=>:q)),)
# NO LONGER SUPPORTED
# colim = pushout(β, γ, type_components=[g,h])
# @test all(is_natural, legs(colim))
# @test ob(colim) == @acset(SetAttr{Symbol}, begin X=1; f=[:q] end)
# h′ = (D=FinFunction(Dict(:z=>:b)),)
# @test_throws ErrorException pushout(β, γ, type_components=[g,h′])

end # module
