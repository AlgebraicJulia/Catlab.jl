module TestWiring

using Base.Test

using CompCat.Doctrine
using CompCat.Diagram.Wiring
import CompCat.Diagram: TikZ

# TikZ
######

Syntax = FreeDaggerCompactCategory
A, B = Syntax.ob(:A), Syntax.ob(:B)
f = Syntax.hom(:f, A, B)
g = Syntax.hom(:g, B, A)

# We can't test that these pictures look right, but we can at least test that
# they exist!
@test isa(diagram_tikz(f), TikZ.Picture)
@test isa(diagram_tikz(compose(f,g)), TikZ.Picture)
@test isa(diagram_tikz(compose(id(A), f, id(B))), TikZ.Picture)
@test isa(diagram_tikz(otimes(f,g)), TikZ.Picture)
@test isa(diagram_tikz(dagger(f)), TikZ.Picture)

end
