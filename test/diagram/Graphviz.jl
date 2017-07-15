module TestGraphviz

using Base.Test
using Catlab.Diagram.Graphviz

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
@test spprint(Edge("n1","n2"; label="bar")) == "n1 -- n2 [label=\"bar\"];"
@test spprint(Edge("n1","n2"; style="dotted", weight="10")) ==
  "n1 -- n2 [style=\"dotted\",weight=\"10\"];"

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

end
