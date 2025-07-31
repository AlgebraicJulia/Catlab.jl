module TestLooseACSetHomSearch 

using Catlab, Test

@present SchSetAttr(FreeSchema) begin
  X::Ob; D::AttrType; f::Attr(X,D)
end
@acset_type SetAttr(SchSetAttr)

const SI = SetAttr{Int}
const 𝒞 = ACSetCategory(LooseACSetCat(SI()))
const 𝒟 = ACSetCategory(ACSetCat(SI()))

s1 = SetAttr{Int}()
add_part!(s1, :X, f=1)
add_part!(s1, :X, f=1)
s2, s3 = deepcopy(s1), deepcopy(s1)
set_subpart!(s2, :f, [2,1])
set_subpart!(s3, :f, [20,10])
@test length(homomorphisms(s2,s3; cat=𝒟))==0
@test length(homomorphisms(s2,s3; type_components=(D=x->10*x,), cat=𝒞))==1
@test length(homomorphisms(s1,s1; type_components=(D=x->x^x,), cat=𝒞))==4

end # module
