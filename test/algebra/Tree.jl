module TestAlgebraTree

using Test
using Catlab.Algebra

# Conversion
############

@test to_formula(:(sin(x))) == Formula(:sin, :x)
@test to_formula(:(sin(2x))) == Formula((:sin, (:*, 2, :x)))
@test to_formula(:(2*sin(2x))) == Formula((:*, 2, (:sin, (:*, 2, :x))))
@test to_formula(:(x == y)) == Formula(:(==), :x, :y)
@test to_formula(:(x -> 2x)) == Formula((:->, :x, (:*, 2, :x)))
@test to_formula(:(A && B)) == Formula(:&, :A, :B)
@test to_formula(:(A || B)) == Formula(:|, :A, :B)

R = Ob(AlgebraicNet, :R)
f = Hom(:sin, R, R)
@test to_formula(f, [:x]) == Formula(:sin, :x)

f = compose(linear(2,R,R), Hom(:sin,R,R))
@test to_formula(f,[:x]) == Formula((:sin, (:*, 2, :x)))
f = compose(linear(2,R,R), Hom(:sin,R,R), linear(2,R,R))
@test to_formula(f,[:x]) == Formula((:*, 2, (:sin, (:*, 2, :x))))

f = compose(Hom(:cos,R,R), Hom(:sin,R,R), Hom(:tan,R,R))
@test to_formula(f,[:x]) == Formula((:tan, (:sin, (:cos, :x))))

f = compose(otimes(id(R),constant(1,R)), mmerge(R))
@test to_formula(f,[:x]) == Formula(:+, :x, 1)

f = compose(otimes(Hom(:cos,R,R), Hom(:sin,R,R)), mmerge(R))
@test to_formula(f,[:x,:y]) == Formula((:+, (:cos, :x), (:sin, :y)))
f = compose(mcopy(R), otimes(Hom(:cos,R,R), Hom(:sin,R,R)), mmerge(R))
@test to_formula(f,[:x]) == Formula((:+, (:cos, :x), (:sin, :x)))

# Evaluation
############

# Standard evaluation.
@test evaluate(Formula(:sin, :x), Dict(:x => pi/2)) == sin(pi/2)
@test evaluate(Formula(:(==), :x, :y), Dict(:x => 1, :y => 1)) == true

# Vectorized evaluation.
x = collect(range(0, stop=2pi, length=10))
@test evaluate(Formula(:sin, :x), Dict(:x => x)) == sin.(x)
@test evaluate(Formula((:*, (:sin, :x), (:cos, :x))), Dict(:x => x)) ==
  @. sin(x) * cos(x)

# Pretty-print
##############

latex(form::Formula) = sprint(show_latex, form)
sexpr(form::Formula) = sprint(show_sexpr, form)

@test latex(Formula(:f, :x , :y)) == "f\\left(x,y\\right)"
@test latex(Formula(:cos, :x)) == "\\mathop{\\mathrm{cos}}\\left(x\\right)"
@test latex(Formula(:+, :x, :y)) == "x + y"
@test latex(Formula(:+, :x, :y, :z)) == "x + y + z"
@test latex(Formula(:-, :x, :y)) == "x - y"
@test latex(Formula(:-, :x)) == "- x"
@test latex(Formula((:-, (:+, :x, :y)))) == "- \\left(x + y\\right)"
@test latex(Formula(:*, :x, :y)) == "x y"
@test latex(Formula(:.*, :x, :y)) == "x y"
@test latex(Formula(:*, 2, :x)) == "2 x"
@test latex(Formula(:*, 2, 2)) == "2 \\cdot 2"
@test latex(Formula(:/, :x, :y)) == "\\frac{x}{y}"
@test latex(Formula(:./, :x, :y)) == "\\frac{x}{y}"
@test latex(Formula((:*, :x, (:+, :y, :z)))) == "x \\left(y + z\\right)"
@test latex(Formula(:^, :x, :y)) == "x^{y}"
@test latex(Formula(:.^, :x, :y)) == "x^{y}"
@test latex(Formula((:^, (:+, :x, :y), 2))) == "\\left(x + y\\right)^{2}"
@test latex(Formula((:^, 2, (:+, :x, :y)))) == "2^{x + y}"
@test latex(Formula((:^, (:^, :x, :a), :b))) == "\\left(x^{a}\\right)^{b}"
@test latex(Formula(:factorial, :x)) == "x !"
@test latex(Formula(:(==), :x, :y)) == "x = y"
@test latex(Formula(:<, :x, :y)) == "x < y"
@test latex(Formula(:<=, :x, :y)) == "x \\leq y"
@test latex(Formula(:&, :A, :B)) == "A \\wedge B"
@test latex(Formula(:|, :A, :B)) == "A \\vee B"
@test latex(Formula(:!, :A)) == "\\neg A"

@test sexpr(Formula(:f)) == "(:f)"
@test sexpr(Formula(:+, :x, :y)) == "(:+ :x :y)"
@test sexpr(Formula((:*, :x, (:+, :y, 1)))) == "(:* :x (:+ :y 1))"

end
