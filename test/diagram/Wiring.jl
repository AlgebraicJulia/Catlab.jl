using CompCat.Syntax
using CompCat.Diagram.Wiring
import CompCat.Diagram: TikZ

using Base.Test

# TikZ
######

A, B = ob_expr(:A), ob_expr(:B)
f = mor_expr(:f, A, B)
g = mor_expr(:g, B, A)

# We can't test that these pictures look right, but we can at least test that
# they exist!
@test isa(diagram_tikz(f), TikZ.Picture)
@test isa(diagram_tikz(compose(f,g)), TikZ.Picture)
@test isa(diagram_tikz(compose(id(A), f, id(B))), TikZ.Picture)
@test isa(diagram_tikz(otimes(f,g)), TikZ.Picture)
