module TestWiringDiagramLayouts

using Test

using Catlab.Doctrines, Catlab.WiringDiagrams
using Catlab.Graphics

box_positions(d::WiringDiagram) = map(box -> box.value.position, boxes(d))
box_values(d::WiringDiagram) = map(box -> box.value.value, boxes(d))

A, B = Ob(FreeSymmetricMonoidalCategory, :A, :B)
f, g = Hom(:f, A, B), Hom(:g, B, A)

# Generators
@test box_values(layout_diagram(f)) == [f]

# Composition
d = layout_diagram(compose(f,g), orientation=LeftToRight)
@test box_values(d) == [f,g]
(fx, fy), (gx, gy) = box_positions(d)
@test fx < gx
@test fy == gy

# Products
d = layout_diagram(otimes(f,g), orientation=LeftToRight)
@test box_values(d) == [f,g]
(fx, fy), (gx, gy) = box_positions(d)
@test fx == gx
@test fy < gy

# Identities
@test box_values(layout_diagram(id(A))) == [id(A)]

end
