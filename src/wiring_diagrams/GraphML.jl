""" Serialize abstract wiring diagrams as GraphML.

Serialization of box, port, and wire values can be overloaded by data type
(see `convert_to_graphml_data` and `convert_from_graphml_data`).

GraphML is the closest thing to a de jure and de facto standard in the space of
graph data formats, supported by a variety of graph applications and libraries.
We depart mildly from the GraphML spec by allowing JSON data attributes for
GraphML nodes, ports, and edges.

References:

- GraphML Primer: http://graphml.graphdrawing.org/primer/graphml-primer.html
- GraphML DTD: http://graphml.graphdrawing.org/specification/dtd.html
"""
module GraphMLWiringDiagrams
export read_graphml, parse_graphml, write_graphml, generate_graphml,
  convert_from_graphml_data, convert_to_graphml_data

using Compat
using DataStructures: OrderedDict
import JSON
using LightXML
using LightGraphs, MetaGraphs

using ..WiringDiagramCore, ..WiringDiagramSerialization
import ..WiringDiagramCore: PortData

# Data types
############

struct GraphMLKey
  id::String
  attr_name::String
  attr_type::String
  scope::String
  default::Union{Some,Nothing}
end
GraphMLKey(id::String, attr_name::String, attr_type::String, scope::String) =
  GraphMLKey(id, attr_name, attr_type, scope, nothing)

struct WriteState
  keys::OrderedDict{Tuple{String,String},GraphMLKey}
  WriteState() = new(OrderedDict{Tuple{String,String},GraphMLKey}())
end

struct ReadState
  keys::OrderedDict{String,GraphMLKey}
  BoxValue::Type
  PortValue::Type
  WireValue::Type
end

# Serialization
###############

""" Write a wiring diagram to a file as GraphML.
"""
function write_graphml(diagram::WiringDiagram, filename::String)
  LightXML.save_file(generate_graphml(diagram), filename)
end

""" Generate GraphML representing a wiring diagram.
"""
function generate_graphml(diagram::WiringDiagram)::XMLDocument
  # Create XML document.
  xdoc = XMLDocument()
  finalizer(free, xdoc) # Destroy all children when document is GC-ed.
  xroot = create_root(xdoc, "graphml")
  set_attributes(xroot, Pair[
    "xmlns" => "http://graphml.graphdrawing.org/xmlns",
    "xmlns:xsi" => "http://www.w3.org/2001/XMLSchema-instance",
    "xsi:schemaLocation" => "http://graphml.graphdrawing.org/xmlns/1.0/graphml.xsd"
  ])
  
  # Create top-level graph element.
  xgraph = new_element("graph")
  set_attribute(xgraph, "edgedefault", "directed")
  
  # Recursively create nodes.
  state = WriteState()
  generate_graphml_node(state, xgraph, diagram, Int[])
  
  # Add attribute keys (data declarations). The keys are collected while
  # writing the nodes and are stored in the state object.
  for key in values(state.keys)
    generate_graphml_key(xroot, key)
  end
  
  add_child(xroot, xgraph)
  return xdoc
end

function generate_graphml_node(
    state::WriteState, xgraph::XMLElement, diagram::WiringDiagram, path::Vector{Int})
  # Create node element for wiring diagram and graph subelement to contain 
  # boxes and wires.
  xnode = new_child(xgraph, "node")
  set_attribute(xnode, "id", box_id(path))
  generate_graphml_ports(state, xnode, diagram)
  
  xsubgraph = new_child(xnode, "graph")
  set_attribute(xsubgraph, "id", string(box_id(path), ":graph"))
  generate_graphml_data(state, xsubgraph, "graph", diagram.value)
  
  # Add node elements for boxes.
  for v in box_ids(diagram)
    generate_graphml_node(state, xsubgraph, box(diagram, v), [path; v])
  end
  
  # Add edge elements for wires.
  for (i, wire) in enumerate(wires(diagram))
    xedge = new_child(xsubgraph, "edge")
    set_attributes(xedge, Pair[
      "id"         => wire_id(path, i),
      "source"     => box_id(diagram, [path; wire.source.box]),
      "sourceport" => port_name(diagram, wire.source),
      "target"     => box_id(diagram, [path; wire.target.box]),
      "targetport" => port_name(diagram, wire.target),
    ])
    generate_graphml_data(state, xedge, "edge", wire.value)
  end
end

function generate_graphml_node(
    state::WriteState, xgraph::XMLElement, box::Box, path::Vector{Int})
  xnode = new_child(xgraph, "node")
  set_attribute(xnode, "id", box_id(path))
  generate_graphml_data(state, xnode, "node", box.value)
  generate_graphml_ports(state, xnode, box)
end

function generate_graphml_ports(state::WriteState, xnode::XMLElement, box::AbstractBox)
  # Write input ports.
  for (i, port) in enumerate(input_ports(box))
    xport = new_child(xnode, "port")
    set_attribute(xport, "name", port_name(InputPort, i))
    generate_graphml_data(state, xport, "port", Dict("portkind" => "input"))
    generate_graphml_data(state, xport, "port", port)
  end
  # Write output ports.
  for (i, port) in enumerate(output_ports(box))
    xport = new_child(xnode, "port")
    set_attribute(xport, "name", port_name(OutputPort, i))
    generate_graphml_data(state, xport, "port", Dict("portkind" => "output"))
    generate_graphml_data(state, xport, "port", port)
  end
end

function generate_graphml_key(xroot::XMLElement, key::GraphMLKey)
  xkey = new_child(xroot, "key")
  set_attributes(xkey, Pair[
    "id" => key.id,
    "for" => key.scope,
    "attr.name" => key.attr_name,
    "attr.type" => key.attr_type,
  ])
  if !isnothing(key.default)
    xdefault = new_child(xkey, "default")
    set_content(xdefault, generate_graphml_data_value(something(key.default)))
  end
end

function generate_graphml_data(state::WriteState, xelem::XMLElement, scope::String, value)
  data = convert_to_graphml_data(value)
  for (attr_name, attr_value) in data
    # Retrieve or create key from state object.
    key = get!(state.keys, (attr_name, scope)) do
      nkeys = length(state.keys)
      id = "d$(nkeys+1)"
      attr_type = generate_graphml_data_type(typeof(attr_value))
      GraphMLKey(id, attr_name, attr_type, scope)
    end
    
    # Write attribute data to <key> element.
    xdata = new_child(xelem, "data")
    set_attribute(xdata, "key", key.id)
    xvalue = generate_graphml_data_value(attr_value)
    (xvalue isa AbstractString ? set_content : add_child)(xdata, xvalue)
  end
end

generate_graphml_data_type(::Type{Bool}) = "boolean"
generate_graphml_data_type(::Type{<:Integer}) = "int"
generate_graphml_data_type(::Type{<:Real}) = "double"
generate_graphml_data_type(::Type{String}) = "string"
generate_graphml_data_type(::Type{Symbol}) = "string"
generate_graphml_data_type(::Type{Dict{String,T}}) where T = "json"
generate_graphml_data_type(::Type{Vector{T}}) where T = "json"

generate_graphml_data_value(x::Number) = string(x)
generate_graphml_data_value(x::String) = x
generate_graphml_data_value(x::Symbol) = string(x)
generate_graphml_data_value(x::Dict) = JSON.json(x)
generate_graphml_data_value(x::Vector) = JSON.json(x)

convert_to_graphml_data(x) = convert_to_graph_data(x)

# Deserialization
#################

""" Read a wiring diagram from a GraphML file.
"""
function read_graphml(
    BoxValue::Type, PortValue::Type, WireValue::Type, filename::String)
  parse_graphml(BoxValue, PortValue, WireValue, LightXML.parse_file(filename))
end

""" Parse a wiring diagram from a GraphML string or XML document.
"""
function parse_graphml(
    BoxValue::Type, PortValue::Type, WireValue::Type, s::AbstractString)
  parse_graphml(BoxValue, PortValue, WireValue, LightXML.parse_string(s))
end
function parse_graphml(::Type{BoxValue}, ::Type{PortValue}, ::Type{WireValue},
    xdoc::XMLDocument)::WiringDiagram where {BoxValue, PortValue, WireValue}
  xroot = root(xdoc)
  @assert name(xroot) == "graphml" "Root element of GraphML document must be <graphml>"
  xgraphs = xroot["graph"]
  @assert length(xgraphs) == 1 "Root element of GraphML document must contain exactly one <graph>"
  xgraph = xgraphs[1]
  xnodes = xgraph["node"]
  @assert length(xnodes) == 1 "Root graph of GraphML document must contain exactly one <node>"
  xnode = xnodes[1]
  
  keys = parse_graphml_keys(xroot)
  state = ReadState(keys, BoxValue, PortValue, WireValue)
  diagram, ports = parse_graphml_node(state, xnode)
  diagram
end

function parse_graphml_node(state::ReadState, xnode::XMLElement)
  # Parse all port elements.
  ports, input_ports, output_ports = parse_graphml_ports(state, xnode)
  
  # Handle special cases: atomic boxes and malformed elements.
  xgraphs = xnode["graph"]
  if length(xgraphs) > 1
    error("Node element can contain at most one <graph> (subgraph element)")
  elseif isempty(xgraphs)
    data = parse_graphml_data(state, xnode)
    value = convert_from_graphml_data(state.BoxValue, data)
    return (Box(value, input_ports, output_ports), ports)
  end
  xgraph = xgraphs[1] 
  
  # If we get here, we're reading a wiring diagram.
  # FIXME: We should not assume that diagram data has same type as box data.
  data = parse_graphml_data(state, xgraph)
  value = isempty(data) ? nothing : convert_from_graph_data(state.BoxValue, data)
  diagram = WiringDiagram(value, input_ports, output_ports)
  all_ports = Dict{Tuple{String,String},Port}()
  for (key, port_data) in ports
    all_ports[key] = port_data.kind == InputPort ?
      Port(input_id(diagram), OutputPort, port_data.port) : 
      Port(output_id(diagram), InputPort, port_data.port)
  end
  
  # Read the node elements.
  for xsubnode in xgraph["node"]
    box, subports = parse_graphml_node(state, xsubnode)
    v = add_box!(diagram, box)
    for (key, port_data) in subports
      all_ports[key] = Port(v, port_data.kind, port_data.port)
    end
  end
  
  # Read the edge elements.
  for xedge in xgraph["edge"]
    data = parse_graphml_data(state, xedge)
    value = convert_from_graphml_data(state.WireValue, data)
    xsource = attribute(xedge, "source", required=true)
    xtarget = attribute(xedge, "target", required=true)
    xsourceport = attribute(xedge, "sourceport", required=true)
    xtargetport = attribute(xedge, "targetport", required=true)
    source = all_ports[(xsource, xsourceport)]
    target = all_ports[(xtarget, xtargetport)]
    add_wire!(diagram, Wire(value, source, target))
  end
  
  (diagram, ports)
end

function parse_graphml_ports(state::ReadState, xnode::XMLElement)
  ports = Dict{Tuple{String,String},PortData}()
  input_ports, output_ports = state.PortValue[], state.PortValue[]
  xnode_id = attribute(xnode, "id", required=true)
  xports = xnode["port"]
  for xport in xports
    xport_name = attribute(xport, "name", required=true)
    data = parse_graphml_data(state, xport)
    port_kind = pop!(data, "portkind")
    value = convert_from_graphml_data(state.PortValue, data)
    if port_kind == "input"
      push!(input_ports, value)
      ports[(xnode_id, xport_name)] = PortData(InputPort, length(input_ports))
    elseif port_kind == "output"
      push!(output_ports, value)
      ports[(xnode_id, xport_name)] = PortData(OutputPort, length(output_ports))
    else
      error("Invalid port kind: $portkind")
    end
  end
  (ports, input_ports, output_ports)
end

function parse_graphml_keys(xroot::XMLElement)
  keys = OrderedDict{String,GraphMLKey}()
  for xkey in xroot["key"]
    # Read attribute ID, name, type, and scope. Both name and type are optional.
    attrs = attributes_dict(xkey)
    id = attrs["id"]
    attr_name = get(attrs, "attr.name", id)
    attr_type = get(attrs, "attr.type", "string")
    scope = get(attrs, "for", "all")
    
    # Read attribute default value.
    xdefaults = xkey["default"]
    default = if isempty(xdefaults)
      nothing
    else
      @assert length(xdefaults) == 1 "GraphML key can have at most one <default>"
      xdefault = xdefaults[1]
      Some(parse_graphml_data_value(Val{Symbol(attr_type)}, content(xdefault)))
    end
    
    keys[id] = GraphMLKey(id, attr_name, attr_type, scope, default)
  end
  keys
end

function parse_graphml_data(keys::AbstractDict, xelem::XMLElement)
  # FIXME: We are not using the default values for the keys.
  data = Dict{String,Any}()
  for xdata in xelem["data"]
    xkey = attribute(xdata, "key", required=true)
    key = keys[xkey]
    data[key.attr_name] = parse_graphml_data_value(
      Val{Symbol(key.attr_type)}, xdata)
  end
  data
end
parse_graphml_data(state::ReadState, xelem::XMLElement) =
  parse_graphml_data(state.keys, xelem)

parse_graphml_data_value(type::Type, xdata::XMLElement) =
  parse_graphml_data_value(type, content(xdata))
parse_graphml_data_value(::Type{Val{:boolean}}, s::String) = parse(Bool, lowercase(s))
parse_graphml_data_value(::Type{Val{:int}}, s::String) = parse(Int, s)
parse_graphml_data_value(::Type{Val{:long}}, s::String) = parse(Int, s)
parse_graphml_data_value(::Type{Val{:float}}, s::String) = parse(Float32, s)
parse_graphml_data_value(::Type{Val{:double}}, s::String) = parse(Float64, s)
parse_graphml_data_value(::Type{Val{:string}}, s::String) = s
parse_graphml_data_value(::Type{Val{:json}}, s::String) = JSON.parse(s)

convert_from_graphml_data(T::Type, data) = convert_from_graph_data(T, data)

# MetaGraphs
############

""" Read an attributed graph (`MetaGraph`) from a GraphML file.

The equivalent of NetworkX's `read_graphml` function.
"""
function read_graphml_metagraph(filename::String; kw...)
  parse_graphml_metagraph(LightXML.parse_file(filename); kw...)
end

""" Parse an attributed graph from a GraphML string or XML document.

The equivalent of NetworkX's `parse_graphml` function.
"""
function parse_graphml_metagraph(s::AbstractString; kw...)
  parse_graphml_metagraph(LightXML.parse_string(s); kw...)
end
function parse_graphml_metagraph(xdoc::XMLDocument; directed::Bool=false,
                                 multigraph::Bool=false)::AbstractMetaGraph
  xroot = root(xdoc)
  @assert name(xroot) == "graphml" "Root element of GraphML document must be <graphml>"
  xgraphs = xroot["graph"]
  @assert length(xgraphs) == 1 "Root element of GraphML document must contain exactly one <graph>"
  xgraph = xgraphs[1]
  
  # Read the GraphML keys.
  keys = parse_graphml_keys(xroot)
  parse_props = xnode::XMLElement ->
    Dict(Symbol(k) => v for (k,v) in parse_graphml_data(keys, xnode))
  
  # Create attributed graph.
  graph = if directed || attribute(xgraph, "edgedefault") == "directed"
    MetaDiGraph()
  else
    MetaGraph()
  end
  set_props!(graph, parse_props(xgraph))
  
  # Read the node elements.
  vertices = Dict{String,Int}()
  for (i, xnode) in enumerate(xgraph["node"])
    node_id = attribute(xnode, "id", required=true)
    vertices[node_id] = i
    add_vertex!(graph, parse_props(xnode))
  end
  
  # Read the edge elements.
  for xedge in xgraph["edge"]
    source_id = attribute(xedge, "source", required=true)
    target_id = attribute(xedge, "target", required=true)
    source, target = vertices[source_id], vertices[target_id]
    if multigraph
      if !has_edge(graph, source, target)
        add_edge!(graph, source, target, Dict(:edges => Dict{Symbol,Any}[]))
      end
      push!(get_prop(graph, source, target, :edges), parse_props(xedge))
    else
      add_edge!(graph, source, target, parse_props(xedge))
    end
  end
  
  graph
end

end
