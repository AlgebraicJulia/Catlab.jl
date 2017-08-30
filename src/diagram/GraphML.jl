""" Serialize abstract wiring diagrams as GraphML.

References:

- GraphML Primer: http://graphml.graphdrawing.org/primer/graphml-primer.html
- GraphML DTD: http://graphml.graphdrawing.org/specification/dtd.html
"""
module GraphML
export read_graphml, write_graphml

using LightXML
using ..Wiring
import ..Wiring: PortEdgeData

const graphml_attribute_types = Dict(
  Bool => "boolean",
  Int32 => "int",
  Int64 => "int",
  Float32 => "double",
  Float64 => "double",
  String => "string",
  Symbol => "string",
)

# Serialization
###############

""" Serialize a wiring diagram to GraphML.
"""
function write_graphml{BoxValue,PortValue,WireValue}(
    ::Type{BoxValue}, ::Type{PortValue}, ::Type{WireValue},
    diagram::WiringDiagram)::XMLDocument
  # FIXME: The type parameters should be attached to `WiringDiagram`,
  # not this method, but that change will require some effort.
  
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
  xkey = new_child(xroot, "key")
  set_attributes(xkey, Pair[
    "id" => "portkind",
    "for" => "port",
    "attr.name" => "portkind",
    "attr.type" => "string"
  ])
  write_graphml_keys(xroot, "node", BoxValue)
  write_graphml_keys(xroot, "edge", WireValue)
  write_graphml_keys(xroot, "port", PortValue)
  
  # Add top-level graph element.
  xgraph = new_child(xroot, "graph")
  set_attribute(xgraph, "edgedefault", "directed")
  
  # Recursively create nodes.
  write_graphml_node(xgraph, "n", diagram)
  return xdoc
end

function write_graphml_node(xgraph::XMLElement, id::String, diagram::WiringDiagram)
  # Create node element for wiring diagram and graph subelement to contain 
  # boxes and wires.
  xnode = new_child(xgraph, "node")
  set_attribute(xnode, "id", id)
  write_graphml_ports(xnode, diagram)
  
  xsubgraph = new_child(xnode, "graph")
  set_attribute(xsubgraph, "id", "$id:")
  
  # Add node elements for boxes.
  for v in box_ids(diagram)
    write_graphml_node(xsubgraph, "$id:n$v", box(diagram, v))
  end
  
  # Add edge elements for wires.
  in_id, out_id = input_id(diagram), output_id(diagram)
  node_id(port::Port) = port.box in (in_id, out_id) ? id : "$id:n$(port.box)"
  port_name(port::Port) = begin
    is_input = port.box in (in_id, out_id) ?
      port.box == in_id : port.kind == InputPort
    is_input ? "in:$(port.port)" : "out:$(port.port)"
  end
  for wire in wires(diagram)
    xedge = new_child(xsubgraph, "edge")
    set_attributes(xedge, Pair[
      "source"     => node_id(wire.source),
      "sourceport" => port_name(wire.source),
      "target"     => node_id(wire.target),
      "targetport" => port_name(wire.target),
    ])
    write_graphml_data(xedge, wire.value)
  end
end
function write_graphml_node(xgraph::XMLElement, id::String, box::Box)
  xnode = new_child(xgraph, "node")
  set_attribute(xnode, "id", id)
  write_graphml_data(xnode, box.value)
  write_graphml_ports(xnode, box)
end

function write_graphml_ports(xnode::XMLElement, box::AbstractBox)
  for (i, port) in enumerate(input_ports(box))
    xport = new_child(xnode, "port")
    set_attribute(xport, "name", "in:$i")
    
    xdata = new_child(xport, "data")
    set_attribute(xdata, "key", "portkind")
    set_content(xdata, "input")
    write_graphml_data(xport, port)
  end
  for (i, port) in enumerate(output_ports(box))
    xport = new_child(xnode, "port")
    set_attribute(xport, "name", "out:$i")
    
    xdata = new_child(xport, "data")
    set_attribute(xdata, "key", "portkind")
    set_content(xdata, "output")
    write_graphml_data(xport, port)
  end
end

function write_graphml_keys(xroot::XMLElement, domain::String, typ::Type)
  xkey = new_child(xroot, "key")
  set_attributes(xkey, Pair[
    "id" => "value",
    "for" => domain,
    "attr.name" => "value",
    "attr.type" => graphml_attribute_types[typ]
  ])
end
write_graphml_keys(xgraph::XMLElement, domain::String, ::Type{Void}) = nothing

function write_graphml_data(xelem::XMLElement, value)
  xdata = new_child(xelem, "data")
  set_attribute(xdata, "key", "value")
  set_content(xdata, string(value))
end
write_graphml_data(xelem::XMLElement, value::Void) = nothing

# Deserialization
#################

struct ReadState
  BoxValue::Type
  PortValue::Type
  WireValue::Type
end

""" Deserialize a wiring diagram from GraphML.
"""
function read_graphml{BoxValue,PortValue,WireValue}(
    ::Type{BoxValue}, ::Type{PortValue}, ::Type{WireValue},
    xdoc::XMLDocument)::WiringDiagram
  xroot = root(xdoc)
  @assert name(xroot) == "graphml" "Root element of GraphML document must be <graphml>"
  xgraphs = xroot["graph"]
  @assert length(xgraphs) == 1 "Root element of GraphML document must contain exactly one <graph>"
  xgraph = xgraphs[1]
  xnodes = xgraph["node"]
  @assert length(xnodes) == 1 "Root graph of GraphML document must contain exactly one <node>"
  xnode = xnodes[1]
  
  state = ReadState(BoxValue, PortValue, WireValue)
  diagram, ports = read_graphml_node(state, xnode)
  return diagram
end

function read_graphml_node(state::ReadState, xnode::XMLElement)
  # Parse all the port elements.
  ports, input_ports, output_ports = read_graphml_ports(state, xnode)
  
  # Handle special cases: atomic boxes and malformed elements.
  xgraphs = xnode["graph"]
  if length(xgraphs) > 1
    error("Node element can contain at most one <graph> (subgraph element)")
  elseif isempty(xgraphs)
    value = read_graphml_data(xnode, state.BoxValue)
    return (Box(value, input_ports, output_ports), ports)
  end
  xgraph = xgraphs[1] 
  
  # If we get here, we're reading a wiring diagram.
  diagram = WiringDiagram(input_ports, output_ports)
  diagram_ports = Dict{Tuple{String,String},Port}()
  for (key, port_data) in ports
    diagram_ports[key] = port_data.kind == InputPort ?
      Port(input_id(diagram), OutputPort, port_data.port) : 
      Port(output_id(diagram), InputPort, port_data.port)
  end
  
  # Read the node elements.
  for xsubnode in xgraph["node"]
    box, subports = read_graphml_node(state, xsubnode)
    v = add_box!(diagram, box)
    for (key, port_data) in subports
      diagram_ports[key] = Port(v, port_data.kind, port_data.port)
    end
  end
  
  # Read the edge elements.
  for xedge in xgraph["edge"]
    value = read_graphml_data(xedge, state.WireValue)
    xsource = (attribute(xedge, "source"), attribute(xedge, "sourceport"))
    xtarget = (attribute(xedge, "target"), attribute(xedge, "targetport"))
    source, target = diagram_ports[xsource], diagram_ports[xtarget]
    add_wire!(diagram, Wire(value, source, target))
  end
  
  return (diagram, ports)
end

function read_graphml_ports(state::ReadState, xnode::XMLElement)
  ports = Dict{Tuple{String,String},PortEdgeData}()
  input_ports, output_ports = state.PortValue[], state.PortValue[]
  xnode_id = attribute(xnode, "id")
  xports = xnode["port"]
  for xport in xports
    xport_name = attribute(xport, "name")
    value = read_graphml_data(xport, state.PortValue)
    port_kind = get_data(xport, "portkind")
    if port_kind == "input"
      push!(input_ports, value)
      ports[(xnode_id, xport_name)] = PortEdgeData(InputPort, length(input_ports))
    elseif port_kind == "output"
      push!(output_ports, value)
      ports[(xnode_id, xport_name)] = PortEdgeData(OutputPort, length(output_ports))
    else
      error("Invalid port kind: $portkind")
    end
  end
  (ports, input_ports, output_ports)
end

function read_graphml_data(xelem::XMLElement, Value::Type)
  parse(Value, get_data(xelem, "value"))
end
read_graphml_data(xelem::XMLElement, ::Type{String}) = get_data(xelem, "value")
read_graphml_data(xelem::XMLElement, ::Type{Symbol}) = Symbol(get_data(xelem, "value"))
read_graphml_data(xelem::XMLElement, ::Type{Void}) = nothing

function get_data(xelem::XMLElement, key::String)::String
  xdata = [ x for x in xelem["data"] if attribute(x,"key") == key ]
  @assert length(xdata) == 1 "Element must contain exactly one <data> with key=\"$key\""
  return content(xdata[1])
end

end
