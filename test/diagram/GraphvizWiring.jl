module TestGraphvizWiring

using Base.Test

using Catlab.Doctrine
using Catlab.Diagram.Wiring
using Catlab.Diagram.GraphvizWiring
import Catlab.Diagram: Graphviz

# We can't test that the graphs look right, but we can test that they exist!
is_digraph(obj) = isa(obj, Graphviz.Graph) && obj.directed

A, B = ob(FreeSymmetricMonoidalCategory, :A, :B)
f = WiringDiagram(hom(:f, A, B))
g = WiringDiagram(hom(:g, B, A))

@test is_digraph(to_graphviz(f))
@test is_digraph(to_graphviz(compose(f,g)))
@test is_digraph(to_graphviz(otimes(f,g)))

end
