module TestLooseHomSearch

using Catlab, Test

@present SchSetAttr(FreeSchema) begin
  X::Ob; D::AttrType; f::Attr(X,D)
end
@acset_type SetAttr(SchSetAttr)

# Loose
s1 = SetAttr{Int}()
add_part!(s1, :X, f=1)
add_part!(s1, :X, f=1)
s2, s3 = deepcopy(s1), deepcopy(s1)
set_subpart!(s2, :f, [2,1])
set_subpart!(s3, :f, [20,10])
@test length(homomorphisms(s2,s3))==0
@test length(homomorphisms(s2,s3; type_components=(D=x->10*x,)))==1
@test homomorphism(s2,s3; type_components=(D=x->10*x,)) isa LooseACSetTransformation
@test length(homomorphisms(s1,s1; type_components=(D=x->x^x,)))==4

end # module
