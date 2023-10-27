module TestGraphvizCategories
using Test

using Catlab.Theories, Catlab.CategoricalAlgebra, Catlab.Graphs
using Catlab.Graphics.GraphvizCategories
using Catlab.Graphics: Graphviz

const stmts = Graphviz.filter_statements

# Categories
############

@present SchSectionRetract(FreeCategory) begin
  (A, B)::Ob
  i::Hom(A, B)
  r::Hom(B, A)
  compose(i, r) == id(A)
end

gv = to_graphviz(SchSectionRetract)
@test stmts(gv, Graphviz.Node, :label) == ["A", "B"]
@test stmts(gv, Graphviz.Edge, :label) == ["i", "r"]

# ℳ-categories.
@present SchSubobject₀(FreeMCategory) begin
  (A, X)::Ob
  ι::Hom(A, X)
end

gv = to_graphviz(SchSubobject₀, edge_attrs=Dict(:arrowhead => "vee"),
                 tight_attrs=Dict(:dir => "both", :arrowtail => "crow"))
@test stmts(gv, Graphviz.Node, :label) == ["A", "X"]
@test stmts(gv, Graphviz.Edge, :arrowtail) == []

@present SchSubobject <: SchSubobject₀ begin
  ::Tight(ι)
end

gv = to_graphviz(SchSubobject, edge_attrs=Dict(:arrowhead => "vee"),
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

gv = to_graphviz(SchWeightedGraph)
@test length(stmts(gv, Graphviz.Node)) == 3
@test stmts(gv, Graphviz.Node, :label) == ["V", "E"]
@test stmts(gv, Graphviz.Node, :xlabel) == ["Weight"]
@test stmts(gv, Graphviz.Edge, :label) == ["src", "tgt", "weight"]

# Functions
###########

A = FinSet(4)
B = FinSet(4)
f = FinFunction([1,2,2,3], A, B)
gv = to_graphviz(f)
@test length(stmts(gv, Graphviz.Subgraph)) == 2
@test length(stmts(gv, Graphviz.Edge)) == 4

# Diagrams
##########

# Diagram with anonymous objects in J
C = FinCat(@acset Graph begin
  V = 3
  E = 2
  src = [1,2]
  tgt = [3,3]
end)
D = FinDomFunctor([:E,:E,:V], [:tgt,:src], C, FinCat(SchSymmetricGraph))
d = Diagram{id}(D)

gv = to_graphviz(d, node_labels=true)

@test stmts(gv, Graphviz.Node, :label) == ["E","E","V"]
@test stmts(gv, Graphviz.Edge, :label) == ["tgt","src"]

# Diagram with named objects in J
C = FinCat(@acset NamedGraph{Symbol,Symbol} begin
  V = 3
  E = 2
  src = [1,2]
  tgt = [3,3]
  vname = [:e1,:e2,:v]
  ename = [:t,:s]
end)
D = FinDomFunctor([:E,:E,:V], [:tgt,:src], C, FinCat(SchSymmetricGraph))
d = Diagram{id}(D)

gv = to_graphviz(d, node_labels=true)

@test stmts(gv, Graphviz.Node, :label) == ["e1:E","e2:E","v:V"]
@test stmts(gv, Graphviz.Edge, :label) == ["tgt","src"]

end
