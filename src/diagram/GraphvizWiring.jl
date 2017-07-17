""" Draw wiring diagrams (aka string diagrams) using Graphivz.
"""
module GraphvizWiring
export to_graphviz

import ...Doctrine: HomExpr
import ..Graphviz
using ..Wiring

# Default Graphviz font. Reference: http://www.graphviz.org/doc/fontfaq.txt
const default_font = "Serif"

# Default node, graph, and edge attributes.
const default_graph_attrs = Graphviz.Attributes(
  :fontname => default_font,
)
const default_node_attrs = Graphviz.Attributes(
  :fontname => default_font,
  :shape => "plain",
)
const default_edge_attrs = Graphviz.Attributes(
  :fontname => default_font,
  :arrowsize => "0.5",
)

""" Render a wiring diagram using Graphviz.
"""
function to_graphviz(f::WiringDiagram;
    graph_name::String="G", labels::Bool=false,
    graph_attrs::Graphviz.Attributes=Graphviz.Attributes(),
    node_attrs::Graphviz.Attributes=Graphviz.Attributes(),
    edge_attrs::Graphviz.Attributes=Graphviz.Attributes())::Graphviz.Graph
  
  # Nodes
  stmts = Graphviz.Statement[
    # Invisible nodes for incoming and outgoing wires.
    Graphviz.Node(node_name(input_id(f)),
                  label=ports_label(Output, length(inputs(f)))),
    Graphviz.Node(node_name(output_id(f)),
                  label=ports_label(Input, length(outputs(f))))
  ]
  for v in box_ids(f)
    # Visible nodes for boxes.
    label = node_label(v, box(f, v))
    push!(stmts, Graphviz.Node(node_name(v), label=label))
  end
  
  # Edges
  for wire in wires(f)
    src, tgt = wire.source, wire.target
    edge = Graphviz.Edge(
      src = node_name(src.box),
      src_port = port_name(src.kind, src.port),
      src_anchor = port_anchor(src.kind),
      tgt = node_name(tgt.box),
      tgt_port = port_name(tgt.kind, tgt.port),
      tgt_anchor = port_anchor(tgt.kind),
    )
    push!(stmts, edge)
  end
  
  Graphviz.Digraph(graph_name, stmts;
    graph_attrs=merge(default_graph_attrs, graph_attrs),
    node_attrs=merge(default_node_attrs, node_attrs),
    edge_attrs=merge(default_edge_attrs, edge_attrs))
end

""" Render a morphism expression as a wiring diagram using Graphviz.
"""
function to_graphviz(f::HomExpr; kw...)::Graphviz.Graph
  to_graphviz(to_wiring_diagram(f); kw...)
end

node_name(v::Int) = "n$v"
port_name(kind::PortKind, port::Int) = string(kind == Input ? "in" : "out", port)
port_anchor(kind::PortKind) = kind == Input ? "n" : "s"

""" Create an "HTML-like" node label for a box.
"""
function node_label(v::Int, box::Box)::Graphviz.Html
  nin, nout = length(inputs(box)), length(outputs(box))
  Graphviz.Html("""
    <TABLE BORDER="0" CELLPADDING="0" CELLSPACING="0">
    <TR><TD>$(ports_label(Input,nin).content)</TD></TR>
    <TR><TD BORDER="1" CELLPADDING="4">$(label(box))</TD></TR>
    <TR><TD>$(ports_label(Output,nout).content)</TD></TR>
    </TABLE>""")
end

""" Create an "HTML-like" label for the input or output ports of a box.
"""
function ports_label(kind::PortKind, nports::Int)::Graphviz.Html
  rows = join("""<TD HEIGHT="0" WIDTH="24" PORT="$(port_name(kind,i))"></TD>"""
              for i in 1:nports)
  Graphviz.Html("""
    <TABLE BORDER="0" CELLPADDING="0" CELLSPACING="0"><TR>$rows</TR></TABLE>""")
end

""" Create a label for the main content of a box.
"""
function label(box::Box)::String
  string(box)
end
function label(box::HomBox)::String
  string(box.expr)
end

end
