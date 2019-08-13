module TestWiringDiagramExpressions

using Test
using LightGraphs

using Catlab.Doctrines, Catlab.WiringDiagrams
import Catlab.WiringDiagrams.WiringDiagramExpressions: series_in_graph

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

g = union(DiGraph(10), PathDiGraph(3))
add_edge!(g,5,6); add_edge!(g,8,9); add_edge!(g,9,10)

@test series_in_graph(g) == Set([[1,2,3],[5,6],[8,9,10]])

end
