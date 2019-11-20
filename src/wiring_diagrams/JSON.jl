""" Serialize abstract wiring diagrams as JSON.

JSON data formats are convenient when programming for the web. Unfortunately, no
standard for JSON graph formats has gained any kind of widespread adoption. We
adopt a format compatible with that used by the KEILER project and its successor
ELK (Eclipse Layout Kernel). This format is roughly feature compatible with
GraphML, supporting nested graphs and ports. It also supports layout information
like node position and size.

References:

- KEILER's JSON graph format:
  https://rtsys.informatik.uni-kiel.de/confluence/display/KIELER/JSON+Graph+Format
- ELK's JSON graph format:
  https://www.eclipse.org/elk/documentation/tooldevelopers/graphdatastructure/jsonformat.html
"""
module JSONWiringDiagrams
export read_json_graph, parse_json_graph, write_json_graph, generate_json_graph,
  convert_from_json_graph_data, convert_to_json_graph_data

using DataStructures: OrderedDict
import JSON

using ..WiringDiagramCore, ..WiringDiagramSerialization
import ..WiringDiagramCore: PortData

const JSONObject = OrderedDict{String,Any}

# Serialization
###############

""" Write a wiring diagram to a file as JSON.
"""
function write_json_graph(diagram::WiringDiagram, filename::String;
                          indent::Union{Int,Nothing}=nothing)
  open(filename, "w") do io
    JSON.print(io, generate_json_graph(diagram), indent)
  end
end

""" Generate a JSON dict representing a wiring diagram.
"""
function generate_json_graph(diagram::WiringDiagram)::AbstractDict
  generate_json_box(diagram, Int[])
end

function generate_json_box(diagram::WiringDiagram, path::Vector{Int})
  json_object_with_value(diagram.value,
    "id" => box_id(path),
    "ports" => generate_json_ports(diagram),
    "children" => [
      generate_json_box(box(diagram, v), [path; v]) for v in box_ids(diagram)
    ],
    "edges" => [
      json_object_with_value(wire.value,
        "id" => wire_id(path, i),
        "source" => box_id(diagram, [path; wire.source.box]),
        "sourcePort" => port_name(diagram, wire.source),
        "target" => box_id(diagram, [path; wire.target.box]),
        "targetPort" => port_name(diagram, wire.target),
      )
      for (i, wire) in enumerate(wires(diagram))
    ],
  )
end

function generate_json_box(box::Box, path::Vector{Int})
  json_object_with_value(box.value,
    "id" => box_id(path),
    "ports" => generate_json_ports(box),
  )
end

function generate_json_ports(box::AbstractBox)::AbstractArray
  [
    [
      json_object_with_value(port,
        "id" => port_name(InputPort, i),
        "portkind" => "input",
      )
      for (i, port) in enumerate(input_ports(box))
    ];
    [
      json_object_with_value(port,
        "id" => port_name(OutputPort, i),
        "portkind" => "output",
      )
      for (i, port) in enumerate(output_ports(box))
    ];
  ]
end

function json_object_with_value(value, args...)
  obj = JSONObject(args...)
  props = convert_to_json_graph_data(value)
  if !isempty(props)
    obj["properties"] = props
  end
  obj
end

convert_to_json_graph_data(x) = convert_to_graph_data(x)

# Deserialization
#################

""" Read a wiring diagram from a JSON file.
"""
function read_json_graph(
    BoxValue::Type, PortValue::Type, WireValue::Type, filename::String)
  parse_json_graph(BoxValue, PortValue, WireValue, JSON.parsefile(filename))
end

""" Parse a wiring diagram from a JSON string or dict.
"""
function parse_json_graph(
    BoxValue::Type, PortValue::Type, WireValue::Type, s::Union{AbstractString,IO})
  parse_json_graph(BoxValue, PortValue, WireValue, JSON.parse(s))
end
function parse_json_graph(
    ::Type{BoxValue}, ::Type{PortValue}, ::Type{WireValue},
    node::AbstractDict)::WiringDiagram where {BoxValue, PortValue, WireValue}
  diagram, ports = parse_json_box(BoxValue, PortValue, WireValue, node)
  diagram
end

function parse_json_box(
    BoxValue::Type, PortValue::Type, WireValue::Type, node::AbstractDict)
  # Read the ports of the box.
  ports, input_ports, output_ports = parse_json_ports(PortValue, node)

  # Dispense with case when node is an atomic box.
  if !haskey(node, "children")
    value = parse_json_graph_data(BoxValue, node)
    return (Box(value, input_ports, output_ports), ports)
  end

  # If we get here, we're reading a wiring diagram.
  # FIXME: We should not assume that diagram data has same type as box data.
  value = haskey(node, "properties") ? parse_json_graph_data(BoxValue, node) : nothing
  diagram = WiringDiagram(value, input_ports, output_ports)
  all_ports = Dict{Tuple{String,String},Port}()
  for (key, port_data) in ports
    all_ports[key] = port_data.kind == InputPort ?
      Port(input_id(diagram), OutputPort, port_data.port) : 
      Port(output_id(diagram), InputPort, port_data.port)
  end

  # Read the nodes recursively.
  for subnode in node["children"]
    box, subports = parse_json_box(BoxValue, PortValue, WireValue, subnode)
    v = add_box!(diagram, box)
    for (key, port_data) in subports
      all_ports[key] = Port(v, port_data.kind, port_data.port)
    end
  end

  # Read the edges.
  for edge in node["edges"]
    value = parse_json_graph_data(WireValue, edge)
    source = all_ports[(edge["source"], edge["sourcePort"])]
    target = all_ports[(edge["target"], edge["targetPort"])]
    add_wire!(diagram, Wire(value, source, target))
  end

  (diagram, ports)
end

function parse_json_ports(PortValue::Type, node::AbstractDict)
  ports = Dict{Tuple{String,String},PortData}()
  input_ports, output_ports = PortValue[], PortValue[]
  node_id = node["id"]
  for port in node["ports"]
    port_id = port["id"]
    port_kind = port["portkind"]
    value = parse_json_graph_data(PortValue, port)
    if port_kind == "input"
      push!(input_ports, value)
      ports[(node_id, port_id)] = PortData(InputPort, length(input_ports))
    elseif port_kind == "output"
      push!(output_ports, value)
      ports[(node_id, port_id)] = PortData(OutputPort, length(output_ports))
    else
      error("Invalid port kind: $portkind")
    end
  end
  (ports, input_ports, output_ports)
end

function parse_json_graph_data(Value::Type, obj::AbstractDict)
  convert_from_json_graph_data(Value, get(obj, "properties", Dict()))
end

convert_from_json_graph_data(T::Type, data) = convert_from_graph_data(T, data)

end
