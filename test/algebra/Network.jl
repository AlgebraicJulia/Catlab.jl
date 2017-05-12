module TestAlgebraicNetwork

using Base.Test
using Catlab.Algebra
using Catlab.Syntax

unicode(expr::BaseExpr) = sprint(show_unicode, expr)
latex(expr::BaseExpr) = sprint(show_latex, expr)

R = ob(AlgebraicNet, :R)

x = collect(linspace(-2,2))
f = hom(:sin,R,R)
@test compile(f)(x) == sin(x)
@test compile(f,args=[:x])(x) == sin(x)
@test compile(f,name=:myfun)(x) == sin(x)
@test compile(f,name=:myfun2,args=[:x])(x) == sin(x)
@test evaluate(f,x) == sin(x)
@test unicode(f) == "sin"
@test latex(f) == "\\mathrm{sin}"

f = compose(linear(2,R,R), hom(:sin,R,R))
@test compile(f)(x) == sin(2x)
@test evaluate(f,x) == sin(2x)
@test unicode(f) == "linear[2]; sin"
@test latex(f) == "\\mathop{\\mathrm{linear}}\\left[2\\right] ; \\mathrm{sin}"

f = compose(linear(2,R,R), hom(:sin,R,R), linear(2,R,R))
@test compile(f)(x) == 2*sin(2x)
@test evaluate(f,x) == 2*sin(2x)

y = collect(linspace(0,4))
f = otimes(hom(:cos,R,R), hom(:sin,R,R))
@test compile(f)(x,y) == (cos(x),sin(y))
@test compile(f,args=[:x,:y])(x,y) == (cos(x),sin(y))
@test evaluate(f,x,y) == (cos(x),sin(y))
@test unicode(f) == "cos⊗sin"
@test latex(f) == "\\mathrm{cos} \\otimes \\mathrm{sin}"

f = braid(R,R)
@test compile(f)(x,y) == (y,x)
@test evaluate(f,x,y) == (y,x)
f = compose(braid(R,R), otimes(hom(:cos,R,R), hom(:sin,R,R)))
@test compile(f)(x,y) == (cos(y),sin(x))
@test evaluate(f,x,y) == (cos(y),sin(x))

f = compose(otimes(id(R),constant(1,R)), mmerge(R))
@test compile(f)(x) == x+1
@test evaluate(f,x) == x+1
@test unicode(f) == "(id[R]⊗1); mmerge[R,2]"
@test latex(f) == "\\left(\\mathrm{id}_{R} \\otimes 1\\right) ; \\nabla_{R,2}"

f = compose(otimes(id(R),constant((1,1),otimes(R,R))), mmerge(R,3))
@test compile(f)(x) ≈ x+2
@test evaluate(f,x) ≈ x+2

f = mcopy(R)
@test compile(f)(x) == (x,x)
@test evaluate(f,x) == (x,x)
f = mcopy(R,3)
@test compile(f)(x) == (x,x,x)
@test evaluate(f,x) == (x,x,x)

f = compose(mcopy(R), otimes(hom(:cos,R,R), hom(:sin,R,R)))
@test compile(f)(x) == (cos(x),sin(x))
@test evaluate(f,x) == (cos(x),sin(x))

z = collect(linspace(-4,0))
f = mmerge(R)
@test compile(f)(x,y) == x+y
@test evaluate(f,x,y) == x+y
f = mmerge(R,3)
@test compile(f)(x,y,z) == x+y+z
@test evaluate(f,x,y,z) == x+y+z

f = compose(mcopy(R), otimes(id(R), delete(R)))
@test compile(f)(x) == x
@test evaluate(f,x) == x
f = compose(otimes(id(R), create(R)), mmerge(R))
@test compile(f)(x) == x
@test evaluate(f,x) == x

# Deeper compositions
f = compose(mcopy(R), otimes(hom(:cos,R,R), hom(:sin,R,R)), mmerge(R))
@test compile(f)(x) == cos(x) + sin(x)
@test evaluate(f,x) == cos(x) + sin(x)

f = compose(mcopy(R), otimes(id(R),hom(:cos,R,R)), hom(:.*,otimes(R,R),R))
@test compile(f)(x) == x .* cos(x)
@test evaluate(f,x) == x .* cos(x)

f = compose(braid(R,R), otimes(id(R),compose(linear(2,R,R),hom(:sin,R,R))),
            hom(:.*,otimes(R,R),R), linear(2,R,R))
@test compile(f)(x,y) == 2y .* sin(2x)
@test evaluate(f,x,y) == 2y .* sin(2x)

# Multidimensional linear maps
A = [1 2; 3 4]
f = compose(linear(A,otimes(R,R),otimes(R,R)), mmerge(R))
target = squeeze(sum([x y]*A', 2), 2)
@test compile(f)(x,y) ≈ target
@test evaluate(f,x,y) ≈ target

# Symbolic coefficients
f = linear(:c, R, R)
f_comp = compile(f)
@test f_comp(x,c=1) == x
@test f_comp(x,c=2) == 2x
f_comp, f_const = compile(f, return_constants=true, vector=true)
@test f_const == [:c]
@test f_comp([x],[2]) == 2x

f = compose(linear(:k,R,R), hom(:sin,R,R), linear(:A,R,R))
f_comp = compile(f)
@test f_comp(x,k=1,A=2) == 2 .* sin(x)
@test f_comp(x,k=2,A=1) == sin(2x)
f_comp, f_const = compile(f, return_constants=true, vector=true)
@test f_const == [:k,:A]
@test f_comp([x],[1,2]) == 2 .* sin(x)
@test f_comp([x],[2,1]) == sin(2x)

f = compose(otimes(id(R),constant(:c,R)), mmerge(R))
f_comp = compile(f,name=:myfun3)
@test f_comp(x,c=2) ≈ x+2

# Automatic differentiation of symbolic coefficients
# Note: Vectorized evaluation not allowed.
x0 = 2.0
f = compose(linear(:a,R,R), hom(:sin,R,R))
f_comp = compile(f, vector=true, order=1)
@test f_comp([x0],[1]) == (sin(x0), [x0 * cos(x0)])
f_grad = compile(f, vector=true, order=1, allorders=false)
f_hess = compile(f, vector=true, order=2, allorders=false)
@test f_grad([x0],[1]) == [x0 * cos(x0)]
@test f_hess([x0],[1]) == reshape([-x0^2 * sin(x0)],(1,1))

f = compose(linear(:k,R,R), hom(:sin,R,R), linear(:A,R,R))
f_grad = compile(f, vector=true, order=1, allorders=false)
f_hess = compile(f, vector=true, order=2, allorders=false)
@test f_grad([x0],[1,1]) == [x0 * cos(x0), sin(x0)]
@test f_hess([x0],[1,1]) == [-x0^2 * sin(x0)  x0*cos(x0); x0*cos(x0)  0]

end
