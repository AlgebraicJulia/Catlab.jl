module TestWiringDiagramExpressions

using Test
using LightGraphs

using Catlab.Doctrines, Catlab.WiringDiagrams
using Catlab.WiringDiagrams.WiringDiagramExpressions: parallel_in_graph,
  series_in_graph

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
@test Set(series_in_graph(g)) == Set([[1,2,3],[5,6],[8,9,10]])

g = DiGraph([Edge(1,2),Edge(2,3),Edge(3,4),Edge(3,5),Edge(4,6),Edge(5,6)])
@test parallel_in_graph(g) == Dict((3 => 6) => [4,5])

end
