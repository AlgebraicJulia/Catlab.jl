module TestGraphvizCategories
using Test

using Catlab, Catlab.Theories, Catlab.CategoricalAlgebra, Catlab.Graphs
using Catlab.Graphs.BasicGraphs: TheoryWeightedGraph
using Catlab.Graphics.GraphvizCategories
using Catlab.Graphics: Graphviz

const stmts = Graphviz.filter_statements

# Categories
############

@present TheorySectionRetract(FreeCategory) begin
  (A, B)::Ob
  i::Hom(A, B)
  r::Hom(B, A)
  compose(i, r) == id(A)
end

gv = to_graphviz(TheorySectionRetract)
@test stmts(gv, Graphviz.Node, :label) == ["A", "B"]
@test stmts(gv, Graphviz.Edge, :label) == ["i", "r"]

# ℳ-categories.
@present TheorySubobject₀(FreeMCategory) begin
  (A, X)::Ob
  ι::Hom(A, X)
end

gv = to_graphviz(TheorySubobject₀, edge_attrs=Dict(:arrowhead => "vee"),
                 tight_attrs=Dict(:dir => "both", :arrowtail => "crow"))
@test stmts(gv, Graphviz.Node, :label) == ["A", "X"]
@test stmts(gv, Graphviz.Edge, :arrowtail) == []

@present TheorySubobject <: TheorySubobject₀ begin
  ::Tight(ι)
end

gv = to_graphviz(TheorySubobject, edge_attrs=Dict(:arrowhead => "vee"),
                 tight_attrs=Dict(:dir => "both", :arrowtail => "crow"))
@test stmts(gv, Graphviz.Edge, :arrowtail) == ["crow"]

# Categories of elements.
el = elements(path_graph(Graph, 2))
gv = to_graphviz(el)
@test stmts(gv, Graphviz.Node, :label) == ["V", "V", "E"]
@test stmts(gv, Graphviz.Edge, :label) == ["src", "tgt"]

gv = to_graphviz(el, node_labels=true, edge_labels=true)
@test stmts(gv, Graphviz.Node, :label) == ["1:V", "2:V", "3:E"]
@test stmts(gv, Graphviz.Edge, :label) == ["1:src", "2:tgt"]

# Schemas
#########

gv = to_graphviz(TheoryWeightedGraph)
@test length(stmts(gv, Graphviz.Node)) == 3
@test stmts(gv, Graphviz.Node, :label) == ["V", "E"]
@test stmts(gv, Graphviz.Node, :xlabel) == ["Weight"]
@test stmts(gv, Graphviz.Edge, :label) == ["src", "tgt", "weight"]

end
