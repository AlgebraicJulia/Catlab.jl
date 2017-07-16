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
  :shape => "rect",
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
  
  stmts = Graphviz.Statement[]
  for v in box_ids(f)
    push!(stmts, to_node(v, box(f,v)))
  end
  for wire in wires(f)
    if !any(in.((wire.source.box, wire.target.box), (input_id(f), output_id(f))))
      push!(stmts, to_edge(wire))
    end
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

""" Create a Graphviz node for a box in a wiring diagram.
"""
function to_node(v::Int, box::Box)::Graphviz.Node
  Graphviz.Node(node_name(v), label=label(box))
end

""" Create a Graphviz edge for a wire in a wiring diagram.
"""
function to_edge(wire::Wire; labels::Bool=false)::Graphviz.Edge
  # TODO: Support wire labels.
  Graphviz.Edge(node_name(wire.source.box), node_name(wire.target.box))
end

node_name(v::Int) = "n$v"

""" Create a node label for the given box.
"""
function label(box::Box)::String
  string(box)
end
function label(box::HomBox)::String
  string(box.expr)
end

end
