module TestGraphviz

using Test
import JSON

using Catlab.CategoricalAlgebra: Graphs
using Catlab.CategoricalAlgebra.Graphs: nv, ne, src, tgt,
  add_vertex!, add_vertices!, add_edge!, add_edges!, get_vprop, get_eprop
using Catlab.Graphics.Graphviz

# Graphviz to property graph
############################

data_path(name::String) = joinpath(@__DIR__, "data", name)

# Undirected simple graph.
doc = open(JSON.parse, data_path("graphviz_graph.json"), "r")
parsed = parse_graphviz(doc)
@test parsed isa Graphs.SymmetricPropertyGraph
@test nv(parsed) == 10
@test ne(parsed) ÷ 2 == 13

# Directed simple graph
doc = open(JSON.parse, data_path("graphviz_digraph.json"), "r")
parsed = parse_graphviz(doc)
@test parsed isa Graphs.PropertyGraph
@test nv(parsed) == 5
@test src(parsed) == [1,1,1,2,3,4]
@test tgt(parsed) == [2,3,4,5,5,5]
@test get_vprop.([parsed], 1:nv(parsed), :name) == ["A", "B", "C", "D", "F"]
@test get_vprop(parsed, 1, :position) == [99, 162]
@test get_vprop(parsed, 1, :size) == [54, 36]
@test get_eprop(parsed, 1, :spline) isa Vector

# Property graph to Graphviz
############################

# Symmetric property graph.
g = Graphs.SymmetricPropertyGraph{String}()
add_vertex!(g, label="v")
add_vertices!(g, 2)
add_edge!(g, 1, 2, xlabel="e")
gv = to_graphviz(g)
@test !gv.directed
nodes = filter(s -> s isa Node, gv.stmts)
edges = filter(s -> s isa Edge, gv.stmts)
@test length(nodes) == 3
@test length(edges) == 1
@test nodes[1].attrs[:label] == "v"
@test edges[1].attrs[:xlabel] == "e"

# Property graph.
g = Graphs.PropertyGraph{String}()
add_vertices!(g, 3); add_edge!(g, 1, 2); add_edge!(g, 2, 3)
gv = to_graphviz(g)
@test gv.directed
@test length(filter(s -> s isa Node, gv.stmts)) == 3
@test length(filter(s -> s isa Edge, gv.stmts)) == 2

# Property graph with multiple edges.
g = Graphs.PropertyGraph{String}()
add_vertices!(g, 2)
add_edge!(g, 1, 2, label="e1")
add_edge!(g, 1, 2, label="e2")
gv = to_graphviz(g)
@test gv.directed
nodes = filter(s -> s isa Node, gv.stmts)
edges = filter(s -> s isa Edge, gv.stmts)
@test length(nodes) == 2
@test length(edges) == 2
@test [ edge.attrs[:label] for edge in edges ] == ["e1", "e2"]

# Graph to Graphviz
###################

# Graph.
g = Graphs.Graph(3)
add_edges!(g, [1,2], [2,3])
gv = to_graphviz(g)
@test gv.directed
nodes = filter(s -> s isa Node, gv.stmts)
@test [ node.attrs[:label] for node in nodes ] == ["", "", ""]

gv = to_graphviz(g, node_labels=true, edge_labels=true)
nodes = filter(s -> s isa Node, gv.stmts)
edges = filter(s -> s isa Edge, gv.stmts)
@test [ node.attrs[:label] for node in nodes ] == ["1", "2", "3"]
@test [ edge.attrs[:label] for edge in edges ] == ["1", "2"]

# Symmetric graph.
g = Graphs.SymmetricGraph(3)
add_edges!(g, [1,2], [2,3])
gv = to_graphviz(g, edge_labels=true)
@test !gv.directed
edges = filter(s -> s isa Edge, gv.stmts)
@test [ edge.attrs[:label] for edge in edges ] == ["(1,3)", "(2,4)"]

# Pretty-print
##############

spprint(expr::Expression) = sprint(pprint, expr)

# Node statement
@test spprint(Node("n")) == "n;"
@test spprint(Node("n"; label="foo")) == "n [label=\"foo\"];"
@test spprint(Node("n"; shape="box", style="filled")) ==
  "n [shape=\"box\",style=\"filled\"];"

# Edge statement
@test spprint(Edge("n1","n2")) == "n1 -- n2;"
@test spprint(Edge("n1","n2"; label="foo")) == "n1 -- n2 [label=\"foo\"];"
@test spprint(Edge("n1","n2"; style="dotted", weight="10")) ==
  "n1 -- n2 [style=\"dotted\",weight=\"10\"];"
@test spprint(Edge(NodeID("n1","p1"), NodeID("n2","p2"))) == "n1:p1 -- n2:p2;"
@test spprint(Edge(NodeID("n1","p1"), NodeID("n2","p2"); label="bar")) ==
  "n1:p1 -- n2:p2 [label=\"bar\"];"
@test spprint(Edge(NodeID("n1","p1","w"), NodeID("n2", "p2", "e"))) ==
  "n1:p1:w -- n2:p2:e;"
@test spprint(Edge("n1","n2","n3")) == "n1 -- n2 -- n3;"
@test spprint(Edge(NodeID("n1"), NodeID("n2"), NodeID("n3"))) ==
  "n1 -- n2 -- n3;"

# Graph statement
graph = Graph("G",
  Node("n1"),
  Node("n2"),
  Edge("n1","n2")
)
@test spprint(graph) == """
graph G {
  n1;
  n2;
  n1 -- n2;
}
"""

graph = Digraph("G",
  Node("n1"),
  Node("n2"),
  Edge("n1","n2")
)
@test spprint(graph) == """
digraph G {
  n1;
  n2;
  n1 -> n2;
}
"""

graph = Digraph("G",
  Node("n1"; label="foo"),
  Node("n2"; label="bar"),
  Edge("n1","n2");
  graph_attrs = Attributes(:rankdir => "LR"),
  node_attrs = Attributes(:shape => "box", :style => "filled"),
  edge_attrs = Attributes(:style => "dotted")
)
@test spprint(graph) == """
digraph G {
  graph [rankdir="LR"];
  node [shape="box",style="filled"];
  edge [style="dotted"];
  n1 [label="foo"];
  n2 [label="bar"];
  n1 -> n2;
}
"""

# Subgraph statement
subgraph = Subgraph("sub", 
  Node("n1"),
  Node("n2"),
  Edge("n1","n2")
)
@test spprint(subgraph) == """
subgraph sub {
  n1;
  n2;
  n1 -- n2;
}"""

subgraph = Subgraph(
  Node("n1"),
  Node("n2"),
  graph_attrs = Attributes(:rank => "same")
)
@test spprint(subgraph) == """
{
  graph [rank="same"];
  n1;
  n2;
}"""

end
