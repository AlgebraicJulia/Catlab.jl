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

The input `f` can also be a morphism expression, which is converted into a
wiring diagram.

# Arguments
- `graph_name="G"`: name of Graphviz digraph
- `labels=false`: whether to label the wires
- `xlabel=false`: whether to use Graphviz xlabels for the wires
  (if `labels` is true)
- `anchor_outer_ports=true`: whether to enforce ordering of input and output
  ports of the outer box (i.e., ordering of incoming and outgoing wires)
- `graph_attrs=default_graph_attrs`: top-level graph attributes
- `node_attrs=default_node_attrs`: top-level node attributes
- `edge_attrs=default_edge_attrs`: top-level edge attributes
"""
function to_graphviz(f::WiringDiagram;
    graph_name::String="G", labels::Bool=false, xlabel::Bool=false,
    anchor_outer_ports::Bool=true,
    graph_attrs::Graphviz.Attributes=Graphviz.Attributes(),
    node_attrs::Graphviz.Attributes=Graphviz.Attributes(),
    edge_attrs::Graphviz.Attributes=Graphviz.Attributes())::Graphviz.Graph
  
  # Nodes
  stmts = Graphviz.Statement[]
  # Invisible nodes for incoming and outgoing wires.
  n_inputs, n_outputs = length(input_ports(f)), length(output_ports(f))
  if n_inputs > 0
    push!(stmts, port_nodes(
      input_id(f), InputPort, n_inputs; anchor=anchor_outer_ports))
  end
  if n_outputs > 0
    push!(stmts, port_nodes(
      output_id(f), OutputPort, n_outputs; anchor=anchor_outer_ports))
  end
  # Visible nodes for boxes.
  for v in box_ids(f)
    box = Wiring.box(f, v)
    node = Graphviz.Node("n$v", label=node_html_label(box), id=node_id(box.value))
    push!(stmts, node)
  end
  
  # Edges
  const graphviz_port = (p::Port) -> begin
    if p.box in (input_id(f), output_id(f))
      return Graphviz.NodeID("n$(p.box)p$(p.port)", port_anchor(p.kind))
    end
    Graphviz.NodeID("n$(p.box)", port_name(p.kind, p.port), port_anchor(p.kind))
  end
  for wire in wires(f)
    # Use the port value to label the wire. We arbitrarily choose the target
    # port. In a well-formed diagram, the source and target ports should
    # yield the same label, but that is not guaranteed.
    # FIXME: Should we start with the wire value instead, if present?
    port = port_value(f, wire.target)
    attrs = Graphviz.Attributes(:id => edge_id(port))
    if labels
      attrs[xlabel ? :xlabel : :label] = edge_label(port)
    end
    edge = Graphviz.Edge(graphviz_port(wire.source),
                         graphviz_port(wire.target); attrs...)
    push!(stmts, edge)
  end
  
  Graphviz.Digraph(graph_name, stmts;
    graph_attrs=merge(default_graph_attrs, graph_attrs),
    node_attrs=merge(default_node_attrs, node_attrs),
    edge_attrs=merge(default_edge_attrs, edge_attrs))
end

function to_graphviz(f::HomExpr; kw...)::Graphviz.Graph
  to_graphviz(to_wiring_diagram(f); kw...)
end

""" Create an "HTML-like" node label for a box.
"""
function node_html_label(box::Box)::Graphviz.Html
  nin, nout = length(input_ports(box)), length(output_ports(box))
  Graphviz.Html("""
    <TABLE BORDER="0" CELLPADDING="0" CELLSPACING="0">
    <TR><TD>$(ports_html_label(InputPort,nin))</TD></TR>
    <TR><TD BORDER="1" CELLPADDING="4">$(node_label(box.value))</TD></TR>
    <TR><TD>$(ports_html_label(OutputPort,nout))</TD></TR>
    </TABLE>""")
end

""" Create an "HTML-like" label for the input or output ports of a box.
"""
function ports_html_label(kind::PortKind, nports::Int)::Graphviz.Html
  cells = if nports > 0
    join("""<TD HEIGHT="0" WIDTH="24" PORT="$(port_name(kind,i))"></TD>"""
         for i in 1:nports)
  else
    """<TD HEIGHT="0" WIDTH="24"></TD>"""
  end
  Graphviz.Html("""
    <TABLE BORDER="0" CELLPADDING="0" CELLSPACING="0"><TR>$cells</TR></TABLE>""")
end

""" Create invisible nodes for the input or output ports of an outer box.
"""
function port_nodes(v::Int, kind::PortKind, nports::Int;
                    anchor::Bool=true)::Graphviz.Subgraph
  @assert nports > 0
  nodes = [ "n$(v)p$(i)" for i in 1:nports ]
  stmts = if anchor
    Graphviz.Statement[ Graphviz.Edge(nodes) ]
  else
    Graphviz.Statement[ Graphviz.Node(node) for node in nodes ]
  end
  Graphviz.Subgraph(
    stmts,
    graph_attrs=Graphviz.Attributes(
      :rank => kind == InputPort ? "source" : "sink",
      :rankdir => "LR",
    ),
    node_attrs=Graphviz.Attributes(
      :style => "invis",
      :shape => "none",
      :label => "",
      :width => "0.333", # == 24/72, the port width in inches
      :height => "0",
    ),
    edge_attrs=Graphviz.Attributes(
      :style => "invis",
    ),
  )
end

port_name(kind::PortKind, port::Int) = string(kind == InputPort ? "in" : "out", port)
port_anchor(kind::PortKind) = kind == InputPort ? "n" : "s"

""" Create a label for the main content of a box.
"""
node_label(box_value::Any) = string(box_value)

""" Create an identifer for a node for downstream use.

It is included in the Graphviz output but is not used internally by Graphviz.
Reference: http://www.graphviz.org/doc/info/attrs.html#d:id
"""
node_id(box_value::Any) = node_label(box_value)

""" Create a label for an edge.
"""
edge_label(port_value::Any) = string(port_value)

""" Create an identifier for an edge for downstream use.

See also `node_id()`.
"""
edge_id(port_value::Any) = edge_label(port_value)

end
