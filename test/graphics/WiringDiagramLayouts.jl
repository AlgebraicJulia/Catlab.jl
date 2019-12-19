module TestWiringDiagramLayouts

using Test

using Catlab.Doctrines, Catlab.WiringDiagrams
using Catlab.Graphics

box_positions(d::WiringDiagram) = map(box -> box.value.position, boxes(d))
box_values(d::WiringDiagram) = map(box -> box.value.value, boxes(d))

A, B = Ob(FreeSymmetricMonoidalCategory, :A, :B)
f, g = Hom(:f, A, B), Hom(:g, B, A)

# Generators
d = layout_diagram(f, orientation=LeftToRight)
@test box_values(d) == [f]
fv = first(box_ids(d))
((f_in_x, f_in_y),) = map(p -> p.position, input_ports(box(d,fv)))
((f_out_x, f_out_y),) = map(p -> p.position, output_ports(box(d,fv)))
@test f_in_x < f_out_x
@test f_in_y == f_out_y

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
