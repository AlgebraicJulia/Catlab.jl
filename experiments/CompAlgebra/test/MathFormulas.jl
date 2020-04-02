module TestMathFormulas

using Test

using Catlab.WiringDiagrams
using CompAlgebra.AlgebraicNets
using CompAlgebra.MathFormulas

# Conversion
############

# Convert Julia expressions to formulas.
@test to_formula(:(sin(x))) == Formula(:sin, :x)
@test to_formula(:(sin(2x))) == Formula((:sin, (:*, 2, :x)))
@test to_formula(:(2*sin(2x))) == Formula((:*, 2, (:sin, (:*, 2, :x))))
@test to_formula(:(x == y)) == Formula(:(==), :x, :y)
@test to_formula(:(x -> 2x)) == Formula((:->, :x, (:*, 2, :x)))
@test to_formula(:(A && B)) == Formula(:&, :A, :B)
@test to_formula(:(A || B)) == Formula(:|, :A, :B)

# Convert algebraic networks to formulas.
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
@test to_formula(mmerge(R,1),[:x]) == :x
@test to_formula(mmerge(R,3),[:x,:y,:z]) == Formula(:+, :x, :y, :z)

f = compose(otimes(Hom(:cos,R,R), Hom(:sin,R,R)), mmerge(R))
@test to_formula(f,[:x,:y]) == Formula((:+, (:cos, :x), (:sin, :y)))
f = compose(mcopy(R), otimes(Hom(:cos,R,R), Hom(:sin,R,R)), mmerge(R))
@test to_formula(f,[:x]) == Formula((:+, (:cos, :x), (:sin, :x)))

w = [ 1 => 1, 2 => 2, 3 => 1, 4 => 2 ]
f = compose(wiring(w, otimes(R,R,R,R), otimes(R,R)), Hom(:*, otimes(R,R), R))
@test to_formula(f,[:w,:x,:y,:z]) == Formula((:*, (:+, :w, :y), (:+, :x, :z)))

f = wiring([ 1 => 1, 1 => 1, 2 => 1 ], otimes(R,R), R)
@test to_formula(f,[:x,:y]) == Formula((:+, (:*, 2, :x), :y))

# Convert formulas to wiring diagrams.
make_box = (value, arity) -> Box(value, repeat([nothing], arity), [nothing])

d = to_wiring_diagram(Formula(:*, :x, :y), [:x, :y])
@test boxes(d) == [ make_box(:*, 2) ]
v_times, = box_ids(d)
@test wires(d) == map(Wire, [
  (input_id(d), 1) => (v_times, 1),
  (input_id(d), 2) => (v_times, 2),
  (v_times, 1) => (output_id(d), 1),
])

d = to_wiring_diagram(Formula((:+, (:cos, :x), (:sin, :x))), [:x])
@test boxes(d) == [ make_box(:cos, 1), make_box(:sin, 1), make_box(:+, 2) ]
v_cos, v_sin, v_plus = box_ids(d)
@test wires(d) == map(Wire, [
  (input_id(d), 1) => (v_cos, 1),
  (input_id(d), 1) => (v_sin, 1),
  (v_cos, 1) => (v_plus, 1),
  (v_sin, 1) => (v_plus, 2),
  (v_plus, 1) => (output_id(d), 1),
])

d = to_wiring_diagram(Formula((:*, (:cos, :x), (:cos, :x))), [:x])
@test boxes(d) == [ make_box(:cos, 1), make_box(:*, 2) ]
v_cos, v_times = box_ids(d)
@test wires(d) == map(Wire, [
  (input_id(d), 1) => (v_cos, 1),
  (v_cos, 1) => (v_times, 1),
  (v_cos, 1) => (v_times, 2),
  (v_times, 1) => (output_id(d), 1),
])

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

# LaTeX pretty-print.
@test latex(Formula(:f, :x , :y)) == "f\\left(x,y\\right)"
@test latex(Formula(:cos, :x)) == "\\cos\\left(x\\right)"
@test latex(Formula(:+, :x, :y)) == "x + y"
@test latex(Formula(:+, :x, :y, :z)) == "x + y + z"
@test latex(Formula(:+, :alpha, :beta)) == "\\alpha + \\beta"
@test latex(Formula(:-, :x, :y)) == "x - y"
@test latex(Formula(:-, :x)) == "- x"
@test latex(Formula(:*, :x, :y)) == "x y"
@test latex(Formula(:.*, :x, :y)) == "x y"
@test latex(Formula(:*, 2, :x)) == "2 x"
@test latex(Formula(:*, 2, 2)) == "2 \\cdot 2"
@test latex(Formula(:/, :x, :y)) == "\\frac{x}{y}"
@test latex(Formula(:./, :x, :y)) == "\\frac{x}{y}"
@test latex(Formula((:*, :x, (:+, :y, :z)))) == "x \\left(y + z\\right)"
@test latex(Formula(:^, :x, :y)) == "x^{y}"
@test latex(Formula(:.^, :x, :y)) == "x^{y}"
@test latex(Formula(:+, Inf, 1)) == "\\infty + 1"
@test latex(Formula((:^, (:+, :x, :y), 2))) == "\\left(x + y\\right)^{2}"
@test latex(Formula((:^, 2, (:+, :x, :y)))) == "2^{x + y}"
@test latex(Formula((:^, (:^, :x, :a), :b))) == "\\left(x^{a}\\right)^{b}"
@test latex(Formula(:factorial, :x)) == "x !"
@test latex(Formula(:(==), :x, :y)) == "x = y"
@test latex(Formula(:<, :x, :y)) == "x < y"
@test latex(Formula(:<=, :x, :y)) == "x \\leq y"
@test latex(Formula(:&, :A, :B)) == "A \\wedge B"
@test latex(Formula(:|, true, false)) == "\\top \\vee \\bot"
@test latex(Formula(:!, :A)) == "\\neg A"

# Operator precedence in LaTeX pretty-print.
@test latex(Formula((:+, (:*, :a, :b), (:*, :c, :d)))) == "a b + c d"
@test latex(Formula((:*, (:+, :a, :b), (:+, :c, :d)))) ==
  "\\left(a + b\\right) \\left(c + d\\right)"
@test latex(Formula((:(==), (:+, :x, :y), (:+, :y, :x)))) == "x + y = y + x"
@test latex(Formula((:&, (:(==), :x, :y), (:(==), :z, :w)))) ==
  "x = y \\wedge z = w"
@test latex(Formula((:-, (:+, :x, :y)))) == "- \\left(x + y\\right)"
@test_skip latex(Formula((:+, :x, (:-, :y)))) == "x + \\left(- y\\right)"
@test latex(Formula((:factorial, (:*, :m, :n)))) == "\\left(m n\\right) !"
@test latex(Formula(:^, -1, :n)) == "\\left(- 1\\right)^{n}"

# S-expression pretty-print.
@test sexpr(Formula(:f)) == "(:f)"
@test sexpr(Formula(:+, :x, :y)) == "(:+ :x :y)"
@test sexpr(Formula((:*, :x, (:+, :y, 1)))) == "(:* :x (:+ :y 1))"

end
