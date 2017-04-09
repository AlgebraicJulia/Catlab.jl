module TestTikZWiring

using Base.Test

using CompCat.Doctrine
using CompCat.Diagram.TikZWiring
using CompCat.Diagram.TikZWiring.Defaults
import CompCat.Diagram: TikZ

# We can't test that these pictures look right, but we can at least test that
# they exist!
ispic(obj) = isa(obj, TikZ.Picture)

Syntax = FreeCategory
A, B = Syntax.ob(:A), Syntax.ob(:B)
f = Syntax.hom(:f, A, B)
g = Syntax.hom(:g, B, A)

@test ispic(wiring_diagram(f))
@test ispic(wiring_diagram(compose(f,g)))
@test ispic(wiring_diagram(compose(id(A), f, id(B))))

Syntax = FreeSymmetricMonoidalCategory
A, B = Syntax.ob(:A), Syntax.ob(:B)
f = Syntax.hom(:f, A, B)
g = Syntax.hom(:g, B, A)
@test ispic(wiring_diagram(otimes(f,g)))
@test ispic(wiring_diagram(compose(otimes(f,g),braid(B,A))))

Syntax = FreeBiproductCategory
A, B = Syntax.ob(:A), Syntax.ob(:B)
f = Syntax.hom(:f, A, B)
g = Syntax.hom(:g, B, A)
@test ispic(wiring_diagram(compose(mcopy(A), otimes(f,f), mmerge(B))))
@test ispic(wiring_diagram(compose(create(A), f, g, delete(A))))

end
