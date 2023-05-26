module TestACSetsGATsInterop
using Test

using Catlab.CategoricalAlgebra
using Catlab.Graphs: SchGraph, SchWeightedGraph

@present SchDendrogram(FreeSchema) begin
  X::Ob
  R::AttrType
  parent::Hom(X,X)
  height::Attr(X,R)
end

@abstract_acset_type AbstractDendrogram
@acset_type Dendrogram(SchDendrogram, index=[:parent]) <: AbstractDendrogram

d = Dendrogram{Int}()
add_parts!(d, :X, 3, height=0)
add_parts!(d, :X, 2, height=[10,20])
set_subpart!(d, 1:3, :parent, 4)
set_subpart!(d, [4,5], :parent, 5)

X, parent, height = SchDendrogram[[:X, :parent, :height]]
@test subpart(d, 3, parent) == 4
@test subpart(d, 3, compose(parent, height)) == 10
@test subpart(d, 3, id(X)) == 3
@test incident(d, 10, compose(parent, height)) == [1,2,3]
@test subpart(d, parent) == [4,4,4,5,5]
@test subpart(d, id(X)) == 1:5
@test subpart(d, compose(parent, height)) == [10,10,10,20,20]

# JSON serialization
#-------------------

function roundtrip_json_acset_schema(pres::Presentation)
  mktempdir() do dir
    path = joinpath(dir, "schema.json")
    write_json_acset_schema(pres, path)
    read_json_acset_schema(path)
  end
end

for schema in [SchGraph, SchWeightedGraph]
  @test roundtrip_json_acset_schema(schema) == schema
end

end
