module TestAlgebra

using Base.Test
using CompCat.Algebra
using CompCat.Syntax

unicode(expr::BaseExpr) = sprint(show_unicode, expr)
latex(expr::BaseExpr) = sprint(show_latex, expr)

R = ob(AlgebraicNet, :Real)
I = munit(AlgebraicNet.Ob)
linear(x) = hom(x, R, R)
constant(x) = hom(x, I, R)

x = linspace(-2,2,100)
f = hom(:sin,R,R)
@test compile(f)(x) == sin(x)
@test unicode(f) == "sin"
@test latex(f) == "\\mathrm{sin}"

f = compose(linear(2), hom(:sin,R,R))
@test compile(f)(x) == sin(2*x)
@test unicode(f) == "2; sin"
@test latex(f) == "2 ; \\mathrm{sin}"

f = compose(linear(2), hom(:sin,R,R), linear(2))
@test compile(f)(x) == 2*sin(2*x)

y = linspace(0,4,100)
f = otimes(hom(:cos,R,R), hom(:sin,R,R))
@test compile(f)(x,y) == [cos(x) sin(y)]

f = compose(otimes(id(R),constant(1)), mmerge(R))
@test compile(f)(x) == x+1

f = mcopy(R)
@test compile(f)(x) == [x x]
f = mcopy(R,3)
@test compile(f)(x) == [x x x]

f = compile(compose(mcopy(R), otimes(hom(:cos,R,R), hom(:sin,R,R))))
@test f(x) == [cos(x) sin(x)]

z = linspace(-4,0,100)
f = mmerge(R)
@test compile(f)(x,y) == x+y
f = mmerge(R,3)
@test compile(f)(x,y,z) == x+y+z

f = compose(mcopy(R), otimes(hom(:cos,R,R), hom(:sin,R,R)), mmerge(R))
@test compile(f)(x) == cos(x) + sin(x)

end
