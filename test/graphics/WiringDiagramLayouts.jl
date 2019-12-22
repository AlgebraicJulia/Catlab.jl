module TestWiringDiagramLayouts

using Test

using Catlab.Doctrines, Catlab.WiringDiagrams
using Catlab.Graphics
using Catlab.Graphics.WiringDiagramLayouts: RectangleShape, CircleShape,
  position

box_layouts(d::WiringDiagram) = map(box -> box.value, boxes(d))
box_values(d::WiringDiagram) = map(layout -> layout.value, box_layouts(d))

# Generators
A, B = Ob(FreeSymmetricMonoidalCategory, :A, :B)
f, g = Hom(:f, A, B), Hom(:g, B, A)

d = layout_diagram(f, orientation=LeftToRight)
@test box_values(d) == [f]
fv = first(box_ids(d))
((f_in_x, f_in_y),) = map(position, input_ports(box(d,fv)))
((f_out_x, f_out_y),) = map(position, output_ports(box(d,fv)))
@test f_in_x < f_out_x
@test f_in_y == f_out_y

# Composition
d = layout_diagram(compose(f,g), orientation=LeftToRight)
@test box_values(d) == [f,g]
(fx, fy), (gx, gy) = map(position, box_layouts(d))
@test fx < gx
@test fy == gy

# Products
d = layout_diagram(otimes(f,g), orientation=LeftToRight)
@test box_values(d) == [f,g]
(fx, fy), (gx, gy) = map(position, box_layouts(d))
@test fx == gx
@test fy < gy

# Identities and braidings
@test box_values(layout_diagram(id(A))) == []
@test box_values(layout_diagram(braid(A,B))) == []

# Diagonals and codiagonals
A, B = Ob(FreeBiproductCategory, :A, :B)

for expr in (mcopy(A), delete(A), mmerge(A), create(A))
  @test map(l -> l.shape, box_layouts(layout_diagram(expr))) == [CircleShape]
end

end
