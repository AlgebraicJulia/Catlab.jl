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
export read_yfiles_diagram

using LightXML
using LightGraphs, MetaGraphs

using ..WiringDiagramCore
using ..GraphMLWiringDiagrams: read_graphml_keys, read_graphml_data
import ..GraphMLWiringDiagrams: read_graphml_data_value

# Deserialization
#################

""" Read a wiring diagram in the GraphML dialect of yEd and yFiles.
"""
function read_yfiles_diagram(xdoc::XMLDocument)::WiringDiagram
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
  
  # Read an attributed graph with the diagram's underlying graph structure.
  graph = read_graphml_metagraph(xdoc, directed=true)
  
  # XXX: Debug
  println(props(graph))
  for v in 1:nv(graph)
    println(props(graph, v))
  end
  for edge in edges(graph)
    println(props(graph, edge))
  end
  
  WiringDiagram([], [])
end
function read_yfiles_diagram(filename::String)
  read_yfiles_diagram(LightXML.parse_file(filename))
end

function read_graphml_data_value(::Type{Val{:yfiles_nodegraphics}}, xdata::XMLElement)
  ynode = first(child_elements(xdata))
  ygeom = find_element(ynode, "Geometry")
  ylabel = find_element(ynode, "NodeLabel")
  Dict(
    :label => content(ylabel),
    :x => float_attribute(ygeom, "x"),
    :y => float_attribute(ygeom, "y"),
    :width => float_attribute(ygeom, "width"),
    :height => float_attribute(ygeom, "height"),
  )
end

function read_graphml_data_value(::Type{Val{:yfiles_edgegraphics}}, xdata::XMLElement)
  yedge = first(child_elements(xdata))
  ypath = find_element(yedge, "Path")
  Dict(
    :source_x => float_attribute(ypath, "sx"),
    :source_y => float_attribute(ypath, "sy"),
    :target_x => float_attribute(ypath, "tx"),
    :target_y => float_attribute(ypath, "ty"),
  )
end

float_attribute(xelem, attr) = parse(Float64, attribute(xelem, attr, required=true))

""" Read attributed graph (`MetaGraph`) from GraphML.

FIXME: This function belongs somewhere else, perhaps in MetaGraphs.jl itself.
"""
function read_graphml_metagraph(xdoc::XMLDocument; directed::Bool=true)::AbstractMetaGraph
  xroot = root(xdoc)
  @assert name(xroot) == "graphml" "Root element of GraphML document must be <graphml>"
  xgraphs = xroot["graph"]
  @assert length(xgraphs) == 1 "Root element of GraphML document must contain exactly one <graph>"
  xgraph = xgraphs[1]
  
  # Read the GraphML keys.
  keys = read_graphml_keys(xroot)
  read_props = xnode::XMLElement ->
    Dict(Symbol(k) => v for (k,v) in read_graphml_data(keys, xnode))
  
  # Create attributed graph.
  graph = if directed || attribute(xgraph, "edgedefault") == "directed"
    MetaDiGraph()
  else
    MetaGraph()
  end
  set_props!(graph, read_props(xgraph))
  
  # Read the node elements.
  vertices = Dict{String,Int}()
  for (i, xnode) in enumerate(xgraph["node"])
    node_id = attribute(xnode, "id", required=true)
    vertices[node_id] = i
    add_vertex!(graph, read_props(xnode))
  end
  
  # Read the edge elements.
  for xedge in xgraph["edge"]
    source_id = attribute(xedge, "source", required=true)
    target_id = attribute(xedge, "target", required=true)
    add_edge!(graph, vertices[source_id], vertices[target_id],
              read_props(xedge))
  end
  
  graph
end

end
