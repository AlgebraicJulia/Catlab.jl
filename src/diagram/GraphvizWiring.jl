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
    port_nodes(input_id(f), length(inputs(f))),
    port_nodes(output_id(f), length(outputs(f))),
  ]
  for v in box_ids(f)
    # Visible nodes for boxes.
    label = node_label(box(f, v))
    push!(stmts, Graphviz.Node("n$v", label=label))
  end
  
  # Edges
  const node_id = (p::Port) -> begin
    if p.box in (input_id(f), output_id(f))
      return Graphviz.NodeID("n$(p.box)p$(p.port)", port_anchor(p.kind))
    end
    Graphviz.NodeID("n$(p.box)", port_name(p.kind, p.port), port_anchor(p.kind))
  end
  for wire in wires(f)
    edge = Graphviz.Edge(node_id(wire.source), node_id(wire.target))
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

""" Create an "HTML-like" node label for a box.
"""
function node_label(box::Box)::Graphviz.Html
  nin, nout = length(inputs(box)), length(outputs(box))
  Graphviz.Html("""
    <TABLE BORDER="0" CELLPADDING="0" CELLSPACING="0">
    <TR><TD>$(ports_label(Input,nin))</TD></TR>
    <TR><TD BORDER="1" CELLPADDING="4">$(label(box))</TD></TR>
    <TR><TD>$(ports_label(Output,nout))</TD></TR>
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

""" Create invisible nodes for the input or output ports of an outer box.
"""
function port_nodes(v::Int, nports::Int)::Graphviz.Subgraph
  nodes = [ "n$(v)p$(i)" for i in 1:nports ]
  Graphviz.Subgraph(
    Graphviz.Edge(nodes),
    graph_attrs=Graphviz.Attributes(:rank => "same", :rankdir => "LR"),
    node_attrs=Graphviz.Attributes(:style => "invis"),
    edge_attrs=Graphviz.Attributes(:style => "invis"),
  )
end

port_name(kind::PortKind, port::Int) = string(kind == Input ? "in" : "out", port)
port_anchor(kind::PortKind) = kind == Input ? "n" : "s"

end
