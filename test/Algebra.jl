module TestAlgebra

using Base.Test
using CompCat.Algebra

R = AlgNetworkExpr.ob(:Real)
I = munit(AlgNetworkExpr.Ob)
linear(x) = AlgNetworkExpr.hom(x, R, R)
constant(x) = AlgNetworkExpr.hom(x, I, R)
func(name::Symbol) = AlgNetworkExpr.hom(name, R, R)

x = linspace(-2,2,100)
f = compile(func(:sin))
@test f(x) == sin(x)

f = compile(compose(linear(2), func(:sin)))
@test f(x) == sin(2*x)

f = compile(compose(linear(2), func(:sin), linear(2)))
@test f(x) == 2*sin(2*x)

y = linspace(0,4,100)
f = compile(otimes(func(:cos), func(:sin)))
@test f(x,y) == [cos(x) sin(y)]

f = compile(compose(otimes(id(R),constant(1)), mmerge(R)))
@test f(x) == x+1

f = compile(mcopy(R))
@test f(x) == [x x]
f = compile(mcopy(R,3))
@test f(x) == [x x x]

f = compile(compose(mcopy(R), otimes(func(:cos), func(:sin))))
@test f(x) == [cos(x) sin(x)]

z = linspace(-4,0,100)
f = compile(mmerge(R))
@test f(x,y) == x+y
f = compile(mmerge(R,3))
@test f(x,y,z) == x+y+z

f = compile(compose(mcopy(R), otimes(func(:cos), func(:sin)), mmerge(R)))
@test f(x) == cos(x) + sin(x)

end
