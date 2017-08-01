""" Serialize abstract wiring diagrams as GraphML.

References:

- GraphML Primer: http://graphml.graphdrawing.org/primer/graphml-primer.html
- GraphML DTD: http://graphml.graphdrawing.org/specification/dtd.html
"""
module GraphML
export to_graphml

using LightXML
using ..Wiring


""" Serialize a wiring diagram to GraphML.
"""
function to_graphml(diagram::WiringDiagram)::XMLDocument
  # Create XML document and top-level graph element.
  xdoc = XMLDocument()
  xroot = create_root(xdoc, "graphml")
  set_attributes(xroot, Pair[
    "xmlns" => "http://graphml.graphdrawing.org/xmlns",
    "xmlns:xsi" => "http://www.w3.org/2001/XMLSchema-instance",
    "xsi:schemaLocation" => "http://graphml.graphdrawing.org/xmlns/1.0/graphml.xsd"
  ])
  xgraph = new_child(xroot, "graph")
  set_attribute(xgraph, "edgedefault", "directed")
  
  # Recursively create nodes.
  add_graphml_box!(xgraph, "d", diagram)
  return xdoc
end

function add_graphml_box!(xgraph::XMLElement, id::String, diagram::WiringDiagram)
  # Create node element for wiring diagram and graph subelement to contain 
  # boxes and wires.
  xnode = add_graphml_node!(xgraph, id, diagram)
  xsubgraph = new_child(xnode, "graph")
  set_attribute(xsubgraph, "id", "$id:")
  
  # Add node elements for boxes.
  for v in box_ids(diagram)
    add_graphml_box!(xsubgraph, "$id:n$v", box(diagram, v))
  end
  
  # Add edge elements for wires.
  outer_ids = (input_id(diagram), output_id(diagram))
  for wire in wires(diagram)
    src, tgt = wire.source, wire.target
    xedge = new_child(xsubgraph, "edge")
    set_attributes(xedge, Pair[
      "source"     => src.box in outer_ids ? id : "$id:n$(src.box)",
      "sourceport" => src.kind == Input ? "in$(src.port)" : "out$(src.port)",
      "target"     => tgt.box in outer_ids ? id : "$id:n$(tgt.box)",
      "targetport" => tgt.kind == Input ? "in$(tgt.port)" : "out$(tgt.port)",
    ])
  end
end
function add_graphml_box!(xgraph::XMLElement, id::String, box::Box)
  add_graphml_node!(xgraph, id, box)
end

function add_graphml_node!(xgraph::XMLElement, id::String, box::Box)
  # Create node element for box.
  xnode = new_child(xgraph, "node")
  set_attribute(xnode, "id", id)
  
  # Add port elements for input and output ports.
  nin, nout = length(input_types(box)), length(output_types(box))
  for i in 1:nin
    xport = new_child(xnode, "port")
    set_attribute(xport, "name", "in$i")
  end
  for i in 1:nout
    xport = new_child(xnode, "port")
    set_attribute(xport, "name", "out$i")
  end
  
  return xnode
end

end
