""" Deserialize abstract wiring diagram from yFiles.

Reads a wiring diagram from the GraphML dialect used by yEd and yFiles. Unlike
the GraphML spec, the yEd data model does not explicitly include ports:

- https://yed.yworks.com/support/qa/102/
- https://yed.yworks.com/support/qa/2531/

We infer the ports of boxes and their order from the geometry of the diagram.
Thus, this module has the nature of a hack. While it may be useful for
interactive and exploratory work, it should not be used in a production system.
"""
module YFilesWiringDiagrams
export read_yfiles_diagram, parse_yfiles_diagram

using Compat
using LightXML
using LightGraphs, MetaGraphs

using ...WiringDiagrams
import ...WiringDiagrams.GraphMLWiringDiagrams: parse_graphml_data_value,
  parse_graphml_metagraph

# Data types
############

struct BoxLayout
  box::Int
  input_coord_map::Dict  # Map from coordinates to input ports
  output_coord_map::Dict # Map from coordinates to output ports
end

# Deserialization
#################

""" Read a wiring diagram from a GraphML file created by yEd and yFiles.
"""
function read_yfiles_diagram(BoxValue::Type, WireValue::Type, filename::String; kw...)
  parse_yfiles_diagram(BoxValue, WireValue, LightXML.parse_file(filename); kw...)
end

""" Parse a wiring diagram from a GraphML string or XML doc created by yFiles.
"""
function parse_yfiles_diagram(BoxValue::Type, WireValue::Type, s::AbstractString; kw...)
  parse_yfiles_diagram(BoxValue, WireValue, LightXML.parse_string(s); kw...)
end
function parse_yfiles_diagram(BoxValue::Type, WireValue::Type, xdoc::XMLDocument;
    direction::Symbol=:vertical, keep_labels::Bool=true)::WiringDiagram
  @assert direction in (:horizontal, :vertical)
  
  # Clean up GraphML keys before reading.
  xroot = root(xdoc)
  for xkey in xroot["key"]
    yfiles_type = attribute(xkey, "yfiles.type")
    if !isnothing(yfiles_type)
      if !has_attribute(xkey, "attr.name")
        set_attribute(xkey, "attr.name", yfiles_type)
      end
      if !has_attribute(xkey, "attr.type")
        set_attribute(xkey, "attr.type", "yfiles_$yfiles_type")
      end
    end
  end
  
  # Read the diagram's underlying graph as an attributed graph.
  graph = parse_graphml_metagraph(xdoc, directed=true, multigraph=true)
  
  # Extract needed information from yFiles' "nodegraphics" and "edgegraphics"
  # and discard the rest. Keep custom data properties, except the blank
  # "description" property inserted by yEd.
  for v in 1:nv(graph)
    v_data = props(graph, v)
    if haskey(v_data, :description) && isempty(v_data[:description])
      delete!(v_data, :description)
    end
    node_graphics = pop!(v_data, :nodegraphics)
    if keep_labels & haskey(node_graphics, :label)
      v_data[:label] = node_graphics[:label]
    end
  end
  for edge in edges(graph)
    for wire_data in get_prop(graph, edge, :edges)
      if haskey(wire_data, :description) && isempty(wire_data[:description])
        delete!(wire_data, :description)
      end
      edge_graphics = pop!(wire_data, :edgegraphics)
      wire_data[:source_coord] = round(Int,
        edge_graphics[direction == :vertical ? :source_x : :source_y])
      wire_data[:target_coord] = round(Int,
        edge_graphics[direction == :vertical ? :target_x : :target_y])
      if keep_labels & haskey(edge_graphics, :label)
        wire_data[:label] = edge_graphics[:label]
      end
    end
  end
  
  # Add boxes and their ports to diagram, including the outer box.
  diagram = WiringDiagram([], [])
  boxes = BoxLayout[]
  for v in 1:nv(graph)
    box_layout = if pop!(props(graph, v), :input, false)
      # Special case: diagram inputs.
      ports, coord_map = infer_output_ports(graph, v)
      diagram.input_ports = ports
      BoxLayout(input_id(diagram), Dict(), coord_map)
    elseif pop!(props(graph, v), :output, false)
      # Special case: diagram outputs.
      ports, coord_map = infer_input_ports(graph, v)
      diagram.output_ports = ports
      BoxLayout(output_id(diagram), coord_map, Dict())
    else
      # Generic case: a box.
      input_ports, input_coord_map = infer_input_ports(graph, v)
      output_ports, output_coord_map = infer_output_ports(graph, v)
      value = convert_from_graphml_data(BoxValue, props(graph, v))
      box_id = add_box!(diagram, Box(value, input_ports, output_ports))
      BoxLayout(box_id, input_coord_map, output_coord_map)
    end
    push!(boxes, box_layout)
  end
  
  # Add wires to diagram.
  for edge in edges(graph)
    source, target = boxes[src(edge)], boxes[dst(edge)]
    for wire_data in get_prop(graph, edge, :edges)
      source_port = source.output_coord_map[pop!(wire_data, :source_coord)]
      target_port = target.input_coord_map[pop!(wire_data, :target_coord)]
      value = convert_from_graphml_data(WireValue, wire_data)
      add_wire!(diagram, Wire(value,
        (source.box, source_port) => (target.box, target_port)))
    end
  end
  
  diagram
end

function infer_input_ports(graph::MetaDiGraph, v::Int)
  in_edges = (get_prop(graph, u, v, :edges) for u in inneighbors(graph, v))
  in_edges = reduce(vcat, in_edges; init=[])
  in_coords = [ edge[:target_coord] for edge in in_edges ]
  infer_ports_from_coordinates(in_coords)
end
function infer_output_ports(graph::MetaDiGraph, v::Int)
  out_edges = (get_prop(graph, v, u, :edges) for u in outneighbors(graph, v))
  out_edges = reduce(vcat, out_edges; init=[])
  out_coords = [ edge[:source_coord] for edge in out_edges ]
  infer_ports_from_coordinates(out_coords)
end

function infer_ports_from_coordinates(coords::Vector{T}) where T
  unique_coords = sort(unique(coords))
  ports = repeat([nothing], length(unique_coords))
  coord_map = Dict{T,Int}(x => i for (i, x) in enumerate(unique_coords))
  (ports, coord_map)
end

function parse_graphml_data_value(::Type{Val{:yfiles_nodegraphics}}, xdata::XMLElement)
  ynode = first(child_elements(xdata)) # e.g., ShapeNode
  ygeom = find_element(ynode, "Geometry")
  data = Dict{Symbol,Any}(
    :x => float_attribute(ygeom, "x"),
    :y => float_attribute(ygeom, "y"),
    :width => float_attribute(ygeom, "width"),
    :height => float_attribute(ygeom, "height"),
  )
  ylabel = find_element(ynode, "NodeLabel")
  if !isnothing(ylabel)
    data[:label] = content(ylabel)
  end
  data
end

function parse_graphml_data_value(::Type{Val{:yfiles_edgegraphics}}, xdata::XMLElement)
  yedge = first(child_elements(xdata)) # e.g., PolyLineEdge
  ypath = find_element(yedge, "Path")
  data = Dict{Symbol,Any}(
    :source_x => float_attribute(ypath, "sx"),
    :source_y => float_attribute(ypath, "sy"),
    :target_x => float_attribute(ypath, "tx"),
    :target_y => float_attribute(ypath, "ty"),
  )
  ylabel = find_element(yedge, "EdgeLabel")
  if !isnothing(ylabel)
    data[:label] = content(ylabel)
  end
  data
end

float_attribute(xelem::XMLElement, name::AbstractString) =
  parse(Float64, attribute(xelem, name, required=true))

end
