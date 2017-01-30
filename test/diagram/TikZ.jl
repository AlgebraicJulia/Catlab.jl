using CompCat.Diagram.TikZ
using Base.Test

function tikz(expr::Expression)
  buf = IOBuffer(); pprint(buf, expr); takebuf_string(buf)
end

# Node statement
@test tikz(Node("f")) == "\\node (f);\n"
@test tikz(Node("f"; props=[Property("circle")])) == "\\node[circle] (f);\n"
@test tikz(Node("f"; props=[Property("circle"),Property("fill","red")])) ==
  "\\node[circle,fill=red] (f);\n"
@test tikz(Node("f"; coord=Coordinate("0","1"))) == "\\node (f) at (0,1);\n"
@test tikz(Node("f"; coord=Coordinate("1","0"), content="fun")) ==
  "\\node (f) at (1,0) {fun};\n"

# Edge statement
@test tikz(Edge("f","g")) == "\\draw (f) to (g);\n"
@test tikz(Edge("f","g"; props=[Property("red")])) == "\\draw[red] (f) to (g);\n"
@test tikz(Edge("f","g"; node=EdgeNode())) == "\\draw (f) to node (g);\n"
@test tikz(Edge("f","g"; node=EdgeNode(;props=[Property("circle")],content="e"))) ==
  "\\draw (f) to node[circle] {e} (g);\n"

# Picture statement
@test tikz(
Picture(
  Node("f"),
  Node("g"),
  Edge("f","g")
)) == """
\\begin{tikzpicture}
  \\node (f);
  \\node (g);
  \\draw (f) to (g);
\\end{tikzpicture}
"""
@test tikz(Picture(Node("f");props=[Property("node distance","1cm")])) == """
\\begin{tikzpicture}[node distance=1cm]
  \\node (f);
\\end{tikzpicture}
"""

# Graph, GraphNode, GraphEdge statements
@test tikz(
Graph(
  GraphNode("f";content="fun"),
  GraphEdge("f","g")
)) == """
\\graph{
  f/\"fun\";
  f -> g;
};
"""
@test tikz(
Graph(
  GraphNode("f";props=[Property("circle")]),
  GraphEdge("f","g";props=[Property("edge label","X")])
)) == """
\\graph{
  f [circle];
  f ->[edge label=X] g;
};
"""
