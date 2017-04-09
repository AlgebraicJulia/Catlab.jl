module TestTikZWiring

using Base.Test

using CompCat.Doctrine
using CompCat.Diagram.TikZWiring
using CompCat.Diagram.TikZWiring.Defaults
import CompCat.Diagram: TikZ

# We can't test that these pictures look right, but we can at least test that
# they exist!

Syntax = FreeCategory
A, B = Syntax.ob(:A), Syntax.ob(:B)
f = Syntax.hom(:f, A, B)
g = Syntax.hom(:g, B, A)

@test isa(wiring_diagram(f), TikZ.Picture)
@test isa(wiring_diagram(compose(f,g)), TikZ.Picture)
@test isa(wiring_diagram(compose(id(A), f, id(B))), TikZ.Picture)

Syntax = FreeSymmetricMonoidalCategory
A, B = Syntax.ob(:A), Syntax.ob(:B)
f = Syntax.hom(:f, A, B)
g = Syntax.hom(:g, B, A)
@test isa(wiring_diagram(otimes(f,g)), TikZ.Picture)
@test isa(wiring_diagram(compose(otimes(f,g),braid(B,A))), TikZ.Picture)

end
