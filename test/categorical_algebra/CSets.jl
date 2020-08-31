module TestCSets
using Test

using Catlab: @present
using Catlab.Theories
using Catlab.CategoricalAlgebra.CSets

@present TheoryDecGraph(FreeSchema) begin
  V::Ob
  E::Ob

  src::Hom(E,V)
  tgt::Hom(E,V)
 
  X::Data

  vdec::Attr(V,X)
  edec::Attr(E,X)
end

const AbstractDecGraph{T} = AbstractACSet{SchemaType(TheoryDecGraph)...,Tuple{T}}

const DecGraph{T} = ACSet{SchemaType(TheoryDecGraph)...,Tuple{T},(:src,:tgt,:vdec)}

g = DecGraph{Symbol}()

@test add_parts!(g,:V,vdec=[:a,:b,:d]) == 1:3

@test subpart(g,:vdec) == [:a,:b,:d]

@test subpart(g,2,:vdec) == :b

@test incident(g,:a,:vdec) == [1]

@test add_parts!(g,:E,src=[1,2],tgt=[2,3],edec=[:f,:g]) == 1:2

@test incident(g,3,:tgt) == [2]

set_subpart!(g,2,:tgt,2)

@test incident(g,3,:tgt) == []

@test incident(g,2,:tgt) == [1,2]

end
