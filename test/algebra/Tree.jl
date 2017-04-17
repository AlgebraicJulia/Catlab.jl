module TestAlgebraTree

using Base.Test
using CompCat.Algebra.Tree

# Pretty-print
##############

latex(form::Formula) = sprint(show_latex, form)
sexpr(form::Formula) = sprint(show_sexpr, form)

@test latex(Formula(:f, :x , :y)) == "f\\left(x,y\\right)"
@test latex(Formula(:cos, :x)) == "\\mathop{\\mathrm{cos}}\\left(x\\right)"
@test latex(Formula(:+, :x, :y)) == "x + y"
@test latex(Formula(:+, :x, :y, :z)) == "x + y + z"
@test latex(Formula(:*, :x, :y)) == "x \\cdot y"
@test latex(Formula(:-, :x, :y)) == "x - y"
@test latex(Formula(:/, :x, :y)) == "\\frac{x}{y}"
@test latex(Formula(:*, :x, Formula(:+, :y, :z))) == "x \\cdot \\left(y + z\\right)"
@test latex(Formula(:^, :x, :y)) == "x^{y}"
@test latex(Formula(:^, Formula(:+, :x, :y), 2)) == "\\left(x + y\\right)^{2}"
@test latex(Formula(:^, 2, Formula(:+, :x, :y))) == "2^{x + y}"

@test sexpr(Formula(:f)) == "(:f)"
@test sexpr(Formula(:+, :x, :y)) == "(:+ :x :y)"
@test sexpr(Formula(:*, :x, Formula(:+, :y, 1))) == "(:* :x (:+ :y 1))"

end
