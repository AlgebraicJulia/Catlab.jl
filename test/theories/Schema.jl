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

A,B,C = map(x->Ob(FreePointedSetSchema,x),[:A,:B,:C])
X = AttrType(FreePointedSetSchema.AttrType,:X)
f,g = Hom(:f,A,B),Hom(:g,B,C)
a = Attr(:a,C,X)
zAB,zBC,zAC,zAX,zBX,zCX = zeromap(A,B),zeromap(B,C),zeromap(A,C),zeromap(A,X),zeromap(B,X),zeromap(C,X)
@test zAC == compose(f,zBC) == compose(zAB,g)
@test zBX == compose(g,zCX) == compose(zBC,a)
@test compose(f,zBC,a) == zAX
