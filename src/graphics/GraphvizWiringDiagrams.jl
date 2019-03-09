""" Draw wiring diagrams (aka string diagrams) using Graphviz.
"""
module GraphvizWiringDiagrams
export to_graphviz

import ...Doctrines: HomExpr
using ...WiringDiagrams, ...WiringDiagrams.WiringDiagramSerialization
import ..Graphviz
import ..Graphviz: to_graphviz

# Default Graphviz font. Reference: http://www.graphviz.org/doc/fontfaq.txt
const default_font = "Serif"

# Default graph, node, edge, and cell attributes.
const default_graph_attrs = Graphviz.Attributes(
  :fontname => default_font,
)
const default_node_attrs = Graphviz.Attributes(
  :fontname => default_font,
  :shape => "none",
  :width => "0",
  :height => "0",
  :margin => "0",
)
const default_edge_attrs = Graphviz.Attributes(
  :arrowsize => "0.5",
  :fontname => default_font,
)
const default_cell_attrs = Graphviz.Attributes(
  :border => "1",
  :cellpadding => "4",
)

""" Render a wiring diagram using Graphviz.

The input `f` can also be a morphism expression, which is converted into a
wiring diagram.

# Arguments
- `graph_name="G"`: name of Graphviz digraph
- `direction=:vertical`: layout direction.
  Either `:vertical` (top to bottom) or `:horizontal` (left to right).
- `node_labels=true`: whether to label the nodes
- `labels=false`: whether to label the edges
- `label_attr=:label`: what kind of edge label to use (if `labels` is true).
  One of `:label`, `:xlabel`, `:headlabel`, or `:taillabel`.
- `port_size="24"`: minimum size of ports on box, in points
- `anchor_outer_ports=true`: whether to enforce ordering of input and output
  ports of the outer box (i.e., ordering of incoming and outgoing wires)
- `graph_attrs=default_graph_attrs`: top-level graph attributes
- `node_attrs=default_node_attrs`: top-level node attributes
- `edge_attrs=default_edge_attrs`: top-level edge attributes
- `cell_attrs=default_cell_attrs`: main cell attributes in node HTML-like label
"""
function to_graphviz(f::WiringDiagram;
    graph_name::String="G", direction::Symbol=:vertical,
    node_labels::Bool=true, labels::Bool=false, label_attr::Symbol=:label,
    port_size::String="24", anchor_outer_ports::Bool=true,
    graph_attrs::Graphviz.Attributes=Graphviz.Attributes(),
    node_attrs::Graphviz.Attributes=Graphviz.Attributes(),
    edge_attrs::Graphviz.Attributes=Graphviz.Attributes(),
    cell_attrs::Graphviz.Attributes=Graphviz.Attributes())::Graphviz.Graph
  @assert direction in (:vertical, :horizontal)
  @assert label_attr in (:label, :xlabel, :headlabel, :taillabel)

  # Graph
  graph_attrs = merge(graph_attrs, Graphviz.Attributes(
    :rankdir => direction == :horizontal ? "LR" : "TB"
  ))
  
  # Nodes
  stmts = Graphviz.Statement[]
  # Invisible nodes for incoming and outgoing wires.
  n_inputs, n_outputs = length(input_ports(f)), length(output_ports(f))
  outer_ports_dir = direction == :vertical ? "LR" : "TB"
  if n_inputs > 0
    push!(stmts, port_nodes(input_id(f), InputPort, n_inputs;
      anchor=anchor_outer_ports, dir=outer_ports_dir))
  end
  if n_outputs > 0
    push!(stmts, port_nodes(output_id(f), OutputPort, n_outputs;
      anchor=anchor_outer_ports, dir=outer_ports_dir))
  end
  # Visible nodes for boxes.
  # Note: The `id` attribute is included in the Graphviz output but is not used
  # internally by Graphviz. It is for use by downstream applications.
  # Reference: http://www.graphviz.org/doc/info/attrs.html#d:id
  cell_attrs = merge(default_cell_attrs, cell_attrs)
  node_html_label = direction == :vertical ?
    node_top_bottom_html_label : node_left_right_html_label
  for v in box_ids(f)
    box = WiringDiagrams.box(f, v)
    nin, nout = length(input_ports(box)), length(output_ports(box))
    text_label = node_labels ? node_label(box.value) : ""
    node = Graphviz.Node(box_id([v]),
      id = box_id([v]),
      comment = node_label(box.value),
      label = node_html_label(nin, nout, text_label,
        attrs = cell_attrs,
        port_size = port_size
      )
    )
    push!(stmts, node)
  end
  
  # Edges
  graphviz_port = (p::Port) -> begin
    anchor = if direction == :vertical
      p.kind == InputPort ? "n" : "s"
    else
      p.kind == InputPort ? "w" : "e"
    end
    if p.box in (input_id(f), output_id(f))
      Graphviz.NodeID(port_node_name(p.box, p.port), anchor)
    else
      Graphviz.NodeID(box_id([p.box]), port_name(p.kind, p.port), anchor)
    end
  end
  for (i, wire) in enumerate(wires(f))
    # Use the port value to label the wire. We take the source port.
    # In most wiring diagrams, the source and target ports should yield the
    # same label, but that is not guaranteed. An advantage of choosing the
    # source port over the target port is that it will carry the
    # "more specific" type when implicit conversions are allowed.
    port = port_value(f, wire.source)
    attrs = Graphviz.Attributes(
      :id => wire_id(Int[], i),
      :comment => edge_label(port),
    )
    if labels
      attrs[label_attr] = edge_label(port)
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

""" Create a top-to-bottom "HTML-like" node label for a box.
"""
function node_top_bottom_html_label(nin::Int, nout::Int, text_label::String;
    attrs::Graphviz.Attributes=Graphviz.Attributes(),
    port_size::String="0")::Graphviz.Html
  Graphviz.Html("""
    <TABLE BORDER="0" CELLPADDING="0" CELLSPACING="0">
    <TR><TD>$(ports_horizontal_html_label(InputPort,nin,port_size))</TD></TR>
    <TR><TD $(html_attributes(attrs))>$(escape_html(text_label))</TD></TR>
    <TR><TD>$(ports_horizontal_html_label(OutputPort,nout,port_size))</TD></TR>
    </TABLE>""")
end

""" Create a left-to-right "HTML-like" node label for a box.
"""
function node_left_right_html_label(nin::Int, nout::Int, text_label::String;
    attrs::Graphviz.Attributes=Graphviz.Attributes(),
    port_size::String="0")::Graphviz.Html
  Graphviz.Html("""
    <TABLE BORDER="0" CELLPADDING="0" CELLSPACING="0">
    <TR>
    <TD>$(ports_vertical_html_label(InputPort,nin,port_size))</TD>
    <TD $(html_attributes(attrs))>$(escape_html(text_label))</TD>
    <TD>$(ports_vertical_html_label(OutputPort,nout,port_size))</TD>
    </TR>
    </TABLE>""")
end

function html_attributes(attrs::Graphviz.Attributes)::String
  join(["$(uppercase(string(k)))=\"$v\"" for (k,v) in attrs], " ")
end

""" Create horizontal "HTML-like" label for the input or output ports of a box.
"""
function ports_horizontal_html_label(kind::PortKind, nports::Int,
    port_size::String="0")::Graphviz.Html
  cols = if nports > 0
    join("""<TD HEIGHT="0" WIDTH="$port_size" PORT="$(port_name(kind,i))"></TD>"""
         for i in 1:nports)
  else
    """<TD HEIGHT="0" WIDTH="$port_size"></TD>"""
  end
  Graphviz.Html("""
    <TABLE BORDER="0" CELLPADDING="0" CELLSPACING="0"><TR>$cols</TR></TABLE>""")
end

""" Create vertical "HTML-like" label for the input or output ports of a box.
"""
function ports_vertical_html_label(kind::PortKind, nports::Int,
    port_size::String="0")::Graphviz.Html
  rows = if nports > 0
    join("""<TR><TD HEIGHT="$port_size" WIDTH="0" PORT="$(port_name(kind,i))"></TD></TR>"""
         for i in 1:nports)
  else
    """<TR><TD HEIGHT="$port_size" WIDTH="0"></TD></TR>"""
  end
  Graphviz.Html("""
    <TABLE BORDER="0" CELLPADDING="0" CELLSPACING="0">$rows</TABLE>""")
end

""" Create invisible nodes for the input or output ports of an outer box.
"""
function port_nodes(v::Int, kind::PortKind, nports::Int;
                    anchor::Bool=true, dir::String="LR")::Graphviz.Subgraph
  @assert nports > 0
  port_width = "$(round(24/72,digits=3))" # port width in inches
  nodes = [ port_node_name(v, i) for i in 1:nports ]
  stmts = Graphviz.Statement[
    Graphviz.Node(nodes[i], id=port_name(kind, i)) for i in 1:nports
  ]
  if anchor
    push!(stmts, Graphviz.Edge(nodes))
  end
  Graphviz.Subgraph(
    stmts,
    graph_attrs=Graphviz.Attributes(
      :rank => kind == InputPort ? "source" : "sink",
      :rankdir => dir,
    ),
    node_attrs=Graphviz.Attributes(
      :style => "invis",
      :shape => "none",
      :label => "",
      :width => dir == "LR" ? port_width : "0",
      :height => dir == "TB" ? port_width : "0",
    ),
    edge_attrs=Graphviz.Attributes(
      :style => "invis",
    ),
  )
end
port_node_name(v::Int, port::Int) = string(box_id([v]), "p", port)

""" Create a label for the main content of a box.
"""
node_label(box_value::Any) = string(box_value)

""" Create a label for an edge.
"""
edge_label(port_value::Any) = string(port_value)

""" Escape special HTML characters: &, <, >, ", '

Borrowed from HttpCommon package: https://github.com/JuliaWeb/HttpCommon.jl
"""
function escape_html(s::AbstractString)
  s = replace(s, "&" => "&amp;")
  s = replace(s, "\"" => "&quot;")
  s = replace(s, "'" => "&#39;")
  s = replace(s, "<" => "&lt;")
  s = replace(s, ">" => "&gt;")
  return s
end

end
