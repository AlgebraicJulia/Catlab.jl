module TestMonoidalSchema

using Test
using Catlab.Present, Catlab.Theories
using Catlab.Theories: MSchemaDesc, MSchemaDescType, MSchemaDescTypeType

@present ThExp(FreeMonoidalSchema) begin
  Sample::Ob
  Feature::Ob
  T::AttrType
  X::Attr(Sample ⊗ Feature, T)
  y::Attr(Sample, T)
end

s = MSchemaDesc(ThExp)

@test s.obs == [:Sample, :Feature]
@test s.attrs == [:X, :y]
@test s.doms[:X] == [:Sample, :Feature]
@test s.codoms[:y] == [:T]

S = MSchemaDescTypeType(s)

@test MSchemaDesc(S) == s

end
