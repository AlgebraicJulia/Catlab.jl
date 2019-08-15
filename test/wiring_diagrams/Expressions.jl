module TestWiringDiagramExpressions

using Test
using LightGraphs

using Catlab.Doctrines, Catlab.WiringDiagrams
using Catlab.WiringDiagrams.WiringDiagramExpressions: find_parallel,
  find_series, transitive_reduction!

A, B, C, D = Ob(FreeSymmetricMonoidalCategory, :A, :B, :C, :D)
f, g, h, k = Hom(:f,A,B), Hom(:g,B,C), Hom(:h,C,D), Hom(:k,D,C)

# Expression -> Diagram
#######################

# Functorality of conversion.
fd, gd = WiringDiagram(f), WiringDiagram(g)
@test to_wiring_diagram(f) == fd
@test to_wiring_diagram(compose(f,g)) == compose(fd,gd)
@test to_wiring_diagram(otimes(f,g)) == otimes(fd,gd)
@test to_wiring_diagram(munit(FreeSymmetricMonoidalCategory.Ob)) == munit(Ports)

# Diagram -> Expression
#######################

function roundtrip(f::HomExpr)
  to_hom_expr(FreeSymmetricMonoidalCategory, to_wiring_diagram(f))
end

# Base cases.
@test roundtrip(f) == f

# Series reduction.
@test roundtrip(compose(f,g)) == compose(f,g)
@test roundtrip(compose(f,g,h)) == compose(f,g,h)

# Parallel reduction.
@test roundtrip(otimes(f,g)) == otimes(f,g)
@test roundtrip(otimes(f,g,h)) == otimes(f,g,h)

# Series-parallel reduction.
@test roundtrip(otimes(compose(f,g),compose(h,k))) ==
  # roundtrip(compose(otimes(f,h),otimes(g,k))) ==
  otimes(compose(f,g),compose(h,k))
@test roundtrip(otimes(compose(f,g),h)) == otimes(compose(f,g),h)
@test roundtrip(otimes(f,compose(g,h))) == otimes(f,compose(g,h))

# Layer -> Expression
#####################

# Identity.
layer = id(NLayer(3))
@test to_hom_expr(layer, repeat([A],3), repeat([A],3)) == id(otimes(A,A,A))

# Graph operations
##################

# Parallel compositions in graph.
graph = DiGraph([Edge(1,2),Edge(2,3),Edge(3,4),Edge(3,5),Edge(4,6),Edge(5,6)])
@test find_parallel(graph) == Dict((3 => 6) => [4,5])

# Series compositions in graph.
graph = union(DiGraph(10), PathDiGraph(3))
add_edge!(graph,5,6); add_edge!(graph,8,9); add_edge!(graph,9,10)
@test Set(find_series(graph)) == Set([[1,2,3],[5,6],[8,9,10]])

# Transitive reduction of DAG.
graph = DiGraph([ Edge(1,2),Edge(1,3),Edge(1,4),Edge(1,5),
                  Edge(2,4),Edge(3,4),Edge(3,5),Edge(4,5) ])
transitive_reduction!(graph)
@test graph == DiGraph([Edge(1,2),Edge(1,3),Edge(2,4),Edge(3,4),Edge(4,5)])

end
