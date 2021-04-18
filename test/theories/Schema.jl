using Test

using Catlab.Present
using Catlab.Theories: CatDescType, AttrDescType

# Schema
########

A, B = Ob(FreeSchema, :A), Ob(FreeSchema, :B)
f, g = Hom(:f, A, B), Hom(:g, B, A)

C = Data(FreeSchema.Data, :C)
x, y = Attr(:x, A, C), Attr(:y, B, C)

@test dom(x) == A
@test codom(x) == C
@test dom(compose(f,y)) == A
@test dom(compose(g,x)) == B
@test compose(f, compose(g,f)) == compose(compose(f,g), f)
@test compose(f, compose(g, x)) == compose(compose(f, g), x)
@test compose(id(A), f) == f 
@test compose(id(A), x) == x

# CatDesc and AttrDesc
######################

@present TheoryDecGraph(FreeSchema) begin
  V::Ob
  E::Ob

  src::Hom(E,V)
  tgt::Hom(E,V)

  X::Data

  vdec::Attr(V,X)
  edec::Attr(E,X)
end

CD = CatDescType(TheoryDecGraph)
AD = AttrDescType(TheoryDecGraph)

@test dom(CD,:src) == :E
@test codom(CD,:tgt) == :V

@test dom(AD,:vdec) == :V
@test codom(AD,:edec) == :X

@test TheoryDecGraph == Presentation(CD, AD)