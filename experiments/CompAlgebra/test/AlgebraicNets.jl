module TestAlgebraicNets

import Pkg
using Test

using Catlab, Catlab.WiringDiagrams.WiringLayers
using CompAlgebra.AlgebraicNets

R = Ob(AlgebraicNet, :R)

# Compilation and evaluation
############################

# Generator
x = collect(range(-2,stop=2,length=50))
f = Hom(:sin,R,R)
f_comp = compile(f)
@test f_comp(x) == sin.(x)
f_comp = compile(f,args=[:x])
@test f_comp(x) == sin.(x)
f_comp = compile(f,name=:myfun)
@test f_comp(x) == sin.(x)
f_comp = compile(f,name=:myfun2,args=[:x])
@test f_comp(x) == sin.(x)
@test evaluate(f,x) == sin.(x)

# Composition
f = compose(linear(2,R,R), Hom(:sin,R,R))
f_comp = compile(f)
@test f_comp(x) == sin.(2x)
@test evaluate(f,x) == sin.(2x)

f = compose(linear(2,R,R), Hom(:sin,R,R), linear(2,R,R))
f_comp = compile(f)
@test f_comp(x) == 2*sin.(2x)
@test evaluate(f,x) == 2*sin.(2x)

# Monoidal product
y = collect(range(0,stop=4,length=50))
f = otimes(Hom(:cos,R,R), Hom(:sin,R,R))
f_comp = compile(f)
@test f_comp(x,y) == (cos.(x),sin.(y))
f_comp = compile(f,args=[:x,:y])
@test f_comp(x,y) == (cos.(x),sin.(y))
@test evaluate(f,x,y) == (cos.(x),sin.(y))

# Braiding
f = braid(R,R)
f_comp = compile(f)
@test f_comp(x,y) == (y,x)
@test evaluate(f,x,y) == (y,x)

f = compose(braid(R,R), otimes(Hom(:cos,R,R), Hom(:sin,R,R)))
f_comp = compile(f)
@test f_comp(x,y) == (cos.(y),sin.(x))
@test evaluate(f,x,y) == (cos.(y),sin.(x))

# Diagonals
f = mcopy(R)
f_comp = compile(f)
@test f_comp(x) == (x,x)
@test evaluate(f,x) == (x,x)

f = mcopy(R,3)
f_comp = compile(f)
@test f_comp(x) == (x,x,x)
@test evaluate(f,x) == (x,x,x)

f = compose(mcopy(R), otimes(id(R), delete(R)))
f_comp = compile(f)
@test f_comp(x) == x
@test evaluate(f,x) == x

f = compose(mcopy(R), otimes(Hom(:cos,R,R), Hom(:sin,R,R)))
f_comp = compile(f)
@test f_comp(x) == (cos.(x),sin.(x))
@test evaluate(f,x) == (cos.(x),sin.(x))

# Codiagonals
z = collect(range(-4,stop=0,length=50))
f = mmerge(R)
f_comp = compile(f)
@test f_comp(x,y) == @. x+y
@test evaluate(f,x,y) == @. x+y

f = mmerge(R,3)
f_comp = compile(f)
@test f_comp(x,y,z) == @. x+y+z
@test evaluate(f,x,y,z) == @. x+y+z

f = compose(otimes(id(R), create(R)), mmerge(R))
f_comp = compile(f)
@test f_comp(x) == x
@test evaluate(f,x) == x

# Wiring layers
wires = [ 1 => 3, 1 => 2, 2 => 2, 3 => 2, 3 => 1 ]
f = wiring(wires, otimes(R,R,R), otimes(R,R,R))
f_comp = compile(f)
@test f_comp(x,y,z) == (z, x+y+z, x)
@test evaluate(f,x,y,z) == (z, x+y+z, x)

# More complex expressions
f = compose(otimes(id(R),constant(1,R)), mmerge(R))
f_comp = compile(f)
@test f_comp(x) == @. x+1
@test evaluate(f,x) == @. x+1

f = compose(otimes(id(R),constant([1,1],otimes(R,R))), mmerge(R,3))
f_comp = compile(f)
@test f_comp(x) ≈ @. x+2
@test evaluate(f,x) ≈ @. x+2

f = compose(mcopy(R), otimes(Hom(:cos,R,R), Hom(:sin,R,R)), mmerge(R))
f_comp = compile(f)
@test f_comp(x) == @. cos(x) + sin(x)
@test evaluate(f,x) == @. cos(x) + sin(x)

f = compose(mcopy(R), otimes(id(R),Hom(:cos,R,R)), Hom(:*,otimes(R,R),R))
f_comp = compile(f)
@test f_comp(x) == @. x * cos(x)
@test evaluate(f,x) == @. x * cos(x)

f = compose(braid(R,R), otimes(id(R),compose(linear(2,R,R),Hom(:sin,R,R))),
            Hom(:*,otimes(R,R),R), linear(2,R,R))
f_comp = compile(f)
@test f_comp(x,y) == @. 2y * sin(2x)
@test evaluate(f,x,y) == @. 2y * sin(2x)

# Multidimensional linear maps
A = [1 2; 3 4]
f = compose(linear(A,otimes(R,R),otimes(R,R)), mmerge(R))
f_comp = compile(f)
target = dropdims(sum([x y]*A', dims=2), dims=2)
@test f_comp(x,y) ≈ target
@test evaluate(f,x,y) ≈ target

# Compilation with symbolic coefficients
f = linear(:c, R, R)
f_comp = compile(f)
@test f_comp(x,c=1) == x
@test f_comp(x,c=2) == 2x
f_comp, f_const = compile(f, return_constants=true, vector=true)
@test f_const == [:c]
@test f_comp([x],[2]) == 2x

f = compose(linear(:k,R,R), Hom(:sin,R,R), linear(:A,R,R))
f_comp = compile(f)
@test f_comp(x,k=1,A=2) == @. 2 * sin(x)
@test f_comp(x,k=2,A=1) == @. sin(2x)
f_comp, f_const = compile(f, return_constants=true, vector=true)
@test f_const == [:k,:A]
@test f_comp([x],[1,2]) == @. 2 * sin(x)
@test f_comp([x],[2,1]) == @. sin(2x)

f = compose(otimes(id(R),constant(:c,R)), mmerge(R))
f_comp = compile(f,name=:myfun3)
@test f_comp(x,c=2) ≈ @. x+2

# Display
#########

unicode(expr::GATExpr) = sprint(show_unicode, expr)
latex(expr::GATExpr) = sprint(show_latex, expr)

# Generator
f = Hom(:sin,R,R)
@test unicode(f) == "sin"
@test latex(f) == "\\mathrm{sin}"

# Composition
f = compose(linear(2,R,R), Hom(:sin,R,R))
@test unicode(f) == "linear{2}; sin"
@test latex(f) == "\\mathop{\\mathrm{linear}}\\left[2\\right] ; \\mathrm{sin}"

# Monoidal product
f = otimes(Hom(:cos,R,R), Hom(:sin,R,R))
@test unicode(f) == "cos⊗sin"
@test latex(f) == "\\mathrm{cos} \\otimes \\mathrm{sin}"

# Diagonals and codiagonals
f = compose(otimes(id(R),constant(1,R)), mmerge(R))
@test unicode(f) == "(id{R}⊗1); mmerge{R,2}"
@test latex(f) == "\\left(\\mathrm{id}_{R} \\otimes 1\\right) ; \\nabla_{R,2}"

end
