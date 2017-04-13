module TestAlgebra

using Base.Test
using CompCat.Algebra

Reals = AlgNetworkExpr.ob(:Real)
constant(x::Number) = AlgNetworkExpr.hom(x, Reals, Reals)
func(name::Symbol) = AlgNetworkExpr.hom(name, Reals, Reals)

x = linspace(-2,2,100)
f = compile(func(:sin))
@test f(x) == sin(x)

f = compile(compose(constant(2), func(:sin)))
@test f(x) == sin(2*x)

f = compile(compose(constant(2), func(:sin), constant(2)))
@test f(x) == 2*sin(2*x)

end
