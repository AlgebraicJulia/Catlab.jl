module TestGraphviz
using Test

using Catlab.Graphics.Graphviz

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

# NodeID/Edge equality
@test Edge("n1","n2") == Edge("n1","n2")
@test Edge(NodeID("n1","p1"), NodeID("n2","p2")) ==
  Edge(NodeID("n1","p1"), NodeID("n2","p2"))
@test NodeID("n1", "p1") == NodeID("n1", "p1")

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

# Label statement
label1 = Label(label="abc")
label2 = Label(labelloc="t", label="abc")
@test spprint(label1) == "label=\"abc\";"
@test spprint(label2) == "labelloc=\"t\";label=\"abc\";"


end
