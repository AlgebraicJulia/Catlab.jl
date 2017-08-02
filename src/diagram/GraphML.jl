""" Serialize abstract wiring diagrams as GraphML.

References:

- GraphML Primer: http://graphml.graphdrawing.org/primer/graphml-primer.html
- GraphML DTD: http://graphml.graphdrawing.org/specification/dtd.html
"""
module GraphML
export to_graphml

using LightXML
using ..Wiring

# Serialization
###############

""" Serialize a wiring diagram to GraphML.
"""
function to_graphml{BoxValue,WireValue,WireType}(
    ::Type{BoxValue}, ::Type{WireValue}, ::Type{WireType},
    diagram::WiringDiagram)::XMLDocument
  # FIXME: The type parameters should be attached to both `WireTypes` and 
  # `WiringDiagram`, not this method, but that change will require some effort.
  
  # Create XML document.
  xdoc = XMLDocument()
  finalizer(xdoc, free) # Destroy all children when document is GC-ed.
  xroot = create_root(xdoc, "graphml")
  set_attributes(xroot, Pair[
    "xmlns" => "http://graphml.graphdrawing.org/xmlns",
    "xmlns:xsi" => "http://www.w3.org/2001/XMLSchema-instance",
    "xsi:schemaLocation" => "http://graphml.graphdrawing.org/xmlns/1.0/graphml.xsd"
  ])
  
  # Add attribute keys (data declarations).
  add_graphml_keys(xroot, "node", BoxValue)
  add_graphml_keys(xroot, "edge", WireValue)
  add_graphml_keys(xroot, "port", WireType)
  
  # Add top-level graph element.
  xgraph = new_child(xroot, "graph")
  set_attribute(xgraph, "edgedefault", "directed")
  
  # Recursively create nodes.
  add_graphml_box(xgraph, "d", diagram)
  return xdoc
end

function add_graphml_keys(xroot::XMLElement, domain::String, typ::Type)
  xkey = new_child(xroot, "key")
  set_attributes(xkey, Pair[
    "id" => "value",
    "for" => domain,
    "attr.name" => "value",
    "attr.type" => graphml_attribute_types[typ]
  ])
end
add_graphml_keys(xgraph::XMLElement, domain::String, ::Type{Void}) = nothing

function add_graphml_data(xelem::XMLElement, value)
  xdata = new_child(xelem, "data")
  set_attribute(xdata, "key", "value")
  set_content(xdata, string(value))
end
add_graphml_data(xelem::XMLElement, value::Void) = nothing

function add_graphml_box(xgraph::XMLElement, id::String, diagram::WiringDiagram)
  # Create node element for wiring diagram and graph subelement to contain 
  # boxes and wires.
  xnode = new_child(xgraph, "node")
  set_attribute(xnode, "id", id)
  add_graphml_ports(xnode, diagram)
  
  xsubgraph = new_child(xnode, "graph")
  set_attribute(xsubgraph, "id", "$id:")
  
  # Add node elements for boxes.
  for v in box_ids(diagram)
    add_graphml_box(xsubgraph, "$id:n$v", box(diagram, v))
  end
  
  # Add edge elements for wires.
  outer_ids = (input_id(diagram), output_id(diagram))
  for wire in wires(diagram)
    src, tgt = wire.source, wire.target
    xedge = new_child(xsubgraph, "edge")
    set_attributes(xedge, Pair[
      "source"     => src.box in outer_ids ? id : "$id:n$(src.box)",
      "sourceport" => src.kind == Input ? "in:$(src.port)" : "out:$(src.port)",
      "target"     => tgt.box in outer_ids ? id : "$id:n$(tgt.box)",
      "targetport" => tgt.kind == Input ? "in:$(tgt.port)" : "out:$(tgt.port)",
    ])
    add_graphml_data(xedge, wire.value)
  end
end
function add_graphml_box(xgraph::XMLElement, id::String, box::Box)
  xnode = new_child(xgraph, "node")
  set_attribute(xnode, "id", id)
  add_graphml_data(xnode, box.value)
  add_graphml_ports(xnode, box)
end

function add_graphml_ports(xnode::XMLElement, box::AbstractBox)
  for (i, wire_type) in enumerate(input_types(box))
    xport = new_child(xnode, "port")
    set_attribute(xport, "name", "in:$i")
    add_graphml_data(xport, wire_type)
  end
  for (i, wire_type) in enumerate(output_types(box))
    xport = new_child(xnode, "port")
    set_attribute(xport, "name", "out:$i")
    add_graphml_data(xport, wire_type)
  end
end

# Deserialization
#################

# Constants
###########

const graphml_attribute_types = Dict(
  Bool => "boolean",
  Int32 => "int",
  Int64 => "int",
  Float32 => "double",
  Float64 => "double",
  String => "string",
  Symbol => "string",
)

const graphml_attribute_types_rev = Dict(
  "boolean" => Bool,
  "int" => Int,
  "long" => Int,
  "float" => Float32,
  "double" => Float64,
  "string" => String,
)

end
