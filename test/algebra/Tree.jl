module TestAlgebraTree

using Base.Test
using Catlab.Algebra.Network, Catlab.Algebra.Tree

# Conversion
############

R = ob(AlgebraicNet.Ob, :R)
f = hom(:sin, R, R)
@test to_formula(f, [:x]) == Formula(:sin, :x)

f = compose(linear(2,R,R), hom(:sin,R,R))
@test to_formula(f,[:x]) == Formula((:sin, (:*, 2, :x)))
f = compose(linear(2,R,R), hom(:sin,R,R), linear(2,R,R))
@test to_formula(f,[:x]) == Formula((:*, 2, (:sin, (:*, 2, :x))))

f = compose(hom(:cos,R,R), hom(:sin,R,R), hom(:tan,R,R))
@test to_formula(f,[:x]) == Formula((:tan, (:sin, (:cos, :x))))

f = compose(otimes(id(R),constant(1,R)), mmerge(R))
@test to_formula(f,[:x]) == Formula(:+, :x, 1)

f = compose(otimes(hom(:cos,R,R), hom(:sin,R,R)), mmerge(R))
@test to_formula(f,[:x,:y]) == Formula((:+, (:cos, :x), (:sin, :y)))
f = compose(mcopy(R), otimes(hom(:cos,R,R), hom(:sin,R,R)), mmerge(R))
@test to_formula(f,[:x]) == Formula((:+, (:cos, :x), (:sin, :x)))

# Pretty-print
##############

latex(form::Formula) = sprint(show_latex, form)
sexpr(form::Formula) = sprint(show_sexpr, form)

@test latex(Formula(:f, :x , :y)) == "f\\left(x,y\\right)"
@test latex(Formula(:cos, :x)) == "\\mathop{\\mathrm{cos}}\\left(x\\right)"
@test latex(Formula(:+, :x, :y)) == "x + y"
@test latex(Formula(:+, :x, :y, :z)) == "x + y + z"
@test latex(Formula(:*, :x, :y)) == "x y"
@test latex(Formula(:*, 2, :x)) == "2 x"
@test latex(Formula(:.*, :x, :y)) == "x \\cdot y"
@test latex(Formula(:.*, 2, :x)) == "2 x"
@test latex(Formula(:-, :x, :y)) == "x - y"
@test latex(Formula(:./, :x, :y)) == "\\frac{x}{y}"
@test latex(Formula((:*, :x, (:+, :y, :z)))) == "x \\left(y + z\\right)"
@test latex(Formula(:^, :x, :y)) == "x^{y}"
@test latex(Formula((:^, (:+, :x, :y), 2))) == "\\left(x + y\\right)^{2}"
@test latex(Formula((:^, 2, (:+, :x, :y)))) == "2^{x + y}"

@test sexpr(Formula(:f)) == "(:f)"
@test sexpr(Formula(:+, :x, :y)) == "(:+ :x :y)"
@test sexpr(Formula((:*, :x, (:+, :y, 1)))) == "(:* :x (:+ :y 1))"

end
