module TestWiringDiagramExpressions

using Test
using Catlab.Doctrines, Catlab.WiringDiagrams

# Expression -> Diagram
#######################

A, B, C, D = Ob(FreeSymmetricMonoidalCategory, :A, :B, :C, :D)
f, g = Hom(:f,A,B), Hom(:g,B,A)

# Functorality of conversion.
fd, gd = WiringDiagram(f), WiringDiagram(g)
@test to_wiring_diagram(f) == fd
@test to_wiring_diagram(compose(f,g)) == compose(fd,gd)
@test to_wiring_diagram(otimes(f,g)) == otimes(fd,gd)
@test to_wiring_diagram(munit(FreeSymmetricMonoidalCategory.Ob)) == munit(Ports)

# Diagram -> Expression
#######################

end
