module TestTikZ

using Test
using Catlab.Graphics.TikZ

# Pretty-print
##############

spprint(expr::Expression) = sprint(pprint, expr)

# Node statement
@test spprint(Node("f")) == "\\node (f) {};"
@test spprint(Node("f"; props=[Property("circle")])) == 
  "\\node[circle] (f) {};"
@test spprint(Node("f"; props=[Property("circle"),Property("fill","red")])) ==
  "\\node[circle,fill=red] (f) {};"
@test spprint(Node("f"; coord=Coordinate("0","1"))) ==
  "\\node (f) at (0,1) {};"
@test spprint(Node("f"; coord=Coordinate("1","0"), content="fun")) ==
  "\\node (f) at (1,0) {fun};"

# Edge statement
@test spprint(Edge("f","g")) == "\\draw (f) to (g);"
@test spprint(Edge("f","g"; props=[Property("red")])) == "\\draw[red] (f) to (g);"
@test spprint(Edge("f","g"; node=EdgeNode())) == "\\draw (f) to node (g);"
@test spprint(Edge("f","g"; node=EdgeNode(;props=[Property("circle")],content="e"))) ==
  "\\draw (f) to node[circle] {e} (g);"
@test spprint(Edge("f","g"; op=PathOperation("to"; props=[Property("out","0")]))) ==
  "\\draw (f) to[out=0] (g);"

# Picture statement
@test spprint(
Picture(
  Node("f"),
  Node("g"),
  Edge("f","g")
)) == """
\\begin{tikzpicture}
  \\node (f) {};
  \\node (g) {};
  \\draw (f) to (g);
\\end{tikzpicture}"""

@test spprint(Picture(Node("f");props=[Property("node distance","1cm")])) == """
\\begin{tikzpicture}[node distance=1cm]
  \\node (f) {};
\\end{tikzpicture}"""

@test spprint( # Nested pictures
Picture(
  Node("outer1"; content=
    Picture(
      Node("inner1"),
      Node("inner2")
    )),
  Node("outer2"; content=
    Picture(
      Node("inner3"),
      Node("inner4")
    ));
  props=[Property("remember picture")]
)) == """
\\begin{tikzpicture}[remember picture]
  \\node (outer1) {
    \\begin{tikzpicture}
      \\node (inner1) {};
      \\node (inner2) {};
    \\end{tikzpicture}
  };
  \\node (outer2) {
    \\begin{tikzpicture}
      \\node (inner3) {};
      \\node (inner4) {};
    \\end{tikzpicture}
  };
\\end{tikzpicture}"""

# Scope statement
@test spprint(
Picture(
  Scope(Node("f"); props=[Property("red")]),
  Scope(Node("g"); props=[Property("blue")]),
  Edge("f","g")
)) == """
\\begin{tikzpicture}
  \\begin{scope}[red]
    \\node (f) {};
  \\end{scope}
  \\begin{scope}[blue]
    \\node (g) {};
  \\end{scope}
  \\draw (f) to (g);
\\end{tikzpicture}"""

# Graph, GraphScope, GraphNode, GraphEdge statements
@test spprint(
Graph(
  GraphNode("f";content="fun"),
  GraphEdge("f","g")
)) == """
\\graph{
  f/\"fun\";
  f -> g;
};"""

@test spprint(
Graph(
  GraphNode("f";props=[Property("circle")]),
  GraphEdge("f","g";props=[Property("edge label","X")])
)) == """
\\graph{
  f [circle];
  f ->[edge label=X] g;
};"""

@test spprint(
Graph(
  GraphScope(
    GraphEdge("a","b"); props=[Property("same layer")]
  ),
  GraphScope(
    GraphEdge("c","d"); props=[Property("same layer")]
  )
)) == """
\\graph{
  {[same layer]
    a -> b;
  };
  {[same layer]
    c -> d;
  };
};"""

# Matrix statement
@test spprint(
MatrixNode(
  [ [[Node("f")]]              [[Edge("g1","g2")]]; 
    [[Node("h1"),Node("h2")]]  [[Node("i1"),Node("i2")]] ];
  props=[Property("draw","red")]
)) == """
\\matrix[draw=red]{
  \\node (f) {}; &
  \\draw (g1) to (g2); \\\\
  \\node (h1) {};
  \\node (h2) {}; &
  \\node (i1) {};
  \\node (i2) {}; \\\\
};"""

end
