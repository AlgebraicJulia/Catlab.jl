module TestAlgebra

using Base.Test
using CompCat.Algebra

R = AlgNetworkExpr.ob(:Real)
constant(x::Number) = AlgNetworkExpr.hom(x, R, R)
func(name::Symbol) = AlgNetworkExpr.hom(name, R, R)

x = linspace(-2,2,100)
f = compile(func(:sin))
@test f(x) == sin(x)

f = compile(compose(constant(2), func(:sin)))
@test f(x) == sin(2*x)

f = compile(compose(constant(2), func(:sin), constant(2)))
@test f(x) == 2*sin(2*x)

y = linspace(0,4,100)
f = compile(otimes(func(:cos), func(:sin)))
@test f(x,y) == [cos(x) sin(y)]

f = compile(mcopy(R))
@test f(x) == [x x]

f = compile(compose(mcopy(R), otimes(func(:cos), func(:sin))))
@test f(x) == [cos(x) sin(x)]

f = compile(plus(R))
@test f(x,y) == x+y

f = compile(compose(mcopy(R), otimes(func(:cos), func(:sin)), plus(R)))
@test f(x) == cos(x) + sin(x)

end
