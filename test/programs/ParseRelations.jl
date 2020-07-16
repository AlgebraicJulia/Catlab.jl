module TestParseRelations
using Test

using Catlab.WiringDiagrams.UndirectedWiringDiagrams
using Catlab.Programs.ParseRelations
using Catlab.Programs.ParseRelations: RelationDiagram, TypedRelationDiagram

# Untyped relations

parsed = @relation (x,z) where (x,y,z) begin
  R(x,y)
  S(y,z)
end

d = RelationDiagram(2)
add_box!(d, 2, name=:R); add_box!(d, 2, name=:S)
add_junctions!(d, 3, variable=[:x,:y,:z])
set_junction!(d, [1,2,2,3])
set_junction!(d, [1,3], outer=true)
@test parsed == d

parsed = @relation ((x,z) where (x,y,z)) -> (R(x,y); S(y,z))
@test parsed == d

parsed = @relation function (x,z) where (x,y,z); R(x,y); S(y,z) end
@test parsed == d

# Typed relations

parsed = @relation (x,y,z) where (x::X, y::Y, z::Z, w::W) begin
  R(x,w)
  S(y,w)
  T(z,w)
end
d = TypedRelationDiagram([:X,:Y,:Z])
add_box!(d, [:X,:W], name=:R)
add_box!(d, [:Y,:W], name=:S)
add_box!(d, [:Z,:W], name=:T)
add_junctions!(d, [:X,:Y,:Z,:W], variable=[:x,:y,:z,:w])
set_junction!(d, [1,4,2,4,3,4])
set_junction!(d, [1,2,3], outer=true)
@test parsed == d

end
