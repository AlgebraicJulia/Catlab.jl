using Test

using Catlab.Present

# Schema
########

A, B = Ob(FreeSchema, :A), Ob(FreeSchema, :B)
f, g = Hom(:f, A, B), Hom(:g, B, A)

C = AttrType(FreeSchema.AttrType, :C)
x, y = Attr(:x, A, C), Attr(:y, B, C)

@test dom(x) == A
@test codom(x) == C
@test dom(compose(f,y)) == A
@test dom(compose(g,x)) == B
@test compose(f, compose(g,f)) == compose(compose(f,g), f)
@test compose(f, compose(g, x)) == compose(compose(f, g), x)
@test compose(id(A), f) == f 
@test compose(id(A), x) == x
