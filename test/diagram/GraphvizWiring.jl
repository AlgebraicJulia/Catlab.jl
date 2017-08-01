module TestGraphvizWiring

using Base.Test
using Catlab.Doctrine
using Catlab.Diagram.Wiring
using Catlab.Diagram.GraphvizWiring
import Catlab.Diagram: Graphviz

is_digraph(obj) = isa(obj, Graphviz.Graph) && obj.directed

function stmts(graph::Graphviz.Graph, stmt_type::Type, attr::Symbol)
  [ stmt.attrs[attr] for stmt in graph.stmts
    if isa(stmt, stmt_type) && haskey(stmt.attrs, attr) ]
end

A, B = Ob(FreeSymmetricMonoidalCategory, :A, :B)
f = WiringDiagram(Hom(:f, A, B))
g = WiringDiagram(Hom(:g, B, A))

graph = to_graphviz(f)
@test is_digraph(graph)
@test stmts(graph, Graphviz.Node, :id) == ["f"]
@test stmts(graph, Graphviz.Edge, :id) == ["A","B"]
@test stmts(graph, Graphviz.Edge, :label) == []
@test stmts(graph, Graphviz.Edge, :xlabel) == []

graph = to_graphviz(f; labels=true)
@test stmts(graph, Graphviz.Edge, :label) == ["A","B"]
@test stmts(graph, Graphviz.Edge, :xlabel) == []

graph = to_graphviz(f; labels=true, xlabel=true)
@test stmts(graph, Graphviz.Edge, :label) == []
@test stmts(graph, Graphviz.Edge, :xlabel) == ["A","B"]

graph = to_graphviz(compose(f,g))
@test is_digraph(graph)
@test stmts(graph, Graphviz.Node, :id) == ["f","g"]

graph = to_graphviz(otimes(f,g))
@test is_digraph(graph)
@test stmts(graph, Graphviz.Node, :id) == ["f","g"]

end
