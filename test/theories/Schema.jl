using Test

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

# Pointed schema
##################

A,B,C = map(x->Ob(FreePtSchema,x),[:A,:B,:C])
X = AttrType(FreePtSchema.AttrType,:X)
f,g = Hom(:f,A,B),Hom(:g,B,C)
a = Attr(:a,C,X)
zAB,zBC,zAC,zAX,zBX,zCX = z(A,B),z(B,C),z(A,C),z(A,X),z(B,X),z(C,X)
@test zAC == compose(f,zBC) == compose(zAB,g)
@test zBX == compose(g,zCX) == compose(zBC,a)
@test compose(f,zBC,a) == zAX
