""" Graphviz support for Catlab's graph types.
"""
module GraphvizGraphs
export parse_graphviz, to_graphviz

using Compat: isnothing
using StaticArrays: StaticVector, SVector

using ...CategoricalAlgebra.Graphs
import ..Graphviz

# Property graphs
#################

""" Parse Graphviz output in JSON format.

Returns a property graph with graph layout and other metadata. Each node has a
position and size.

All units are in points. Note that Graphviz has 72 points per inch.
"""
function parse_graphviz(doc::AbstractDict)::AbstractPropertyGraph
  graph = doc["directed"] ? PropertyGraph{Any}() : SymmetricPropertyGraph{Any}()
  nsubgraphs = doc["_subgraph_cnt"] # Subgraphs are ignored.

  # Graph-level layout: bounds and padding.
  # It seems, but is not documented, that the first two numbers in the Graphviz
  # bounding box are always zero.
  set_gprops!(graph,
    bounds = SVector{2}(parse_vector(doc["bb"])[3:4]),
    pad = 72*parse_point(get(doc, "pad", "0,0")),
    rankdir = get(doc, "rankdir", "TB"),
  )

  # Add vertex for each Graphviz node.
  node_keys = ("id", "name", "comment", "label", "shape", "style")
  for node in doc["objects"][nsubgraphs+1:end]
    props = Dict{Symbol,Any}(
      Symbol(k) => node[k] for k in node_keys if haskey(node, k))
    props[:position] = parse_point(node["pos"])
    props[:size] = 72*SVector(
      parse(Float64, node["width"]),
      parse(Float64, node["height"])
    )
    add_vertex!(graph, props)
  end

  # Add edge for each Graphviz edge.
  edge_keys = ("id", "comment", "label", "xlabel", "headlabel", "taillabel",
               "headport", "tailport")
  for edge in doc["edges"]
    if get(edge, "style", nothing) == "invis"
      # Omit invisible edges, which are used to tweak the layout in Graphviz.
      continue
    end
    props = Dict{Symbol,Any}(
      Symbol(k) => edge[k] for k in edge_keys if haskey(edge, k))
    props[:spline] = parse_spline(edge["pos"])
    src = edge["tail"] - nsubgraphs + 1
    tgt = edge["head"] - nsubgraphs + 1
    add_edge!(graph, src, tgt, props)
  end

  graph
end

""" Parse an array of floats in Graphviz's comma-separated format.
"""
parse_vector(s::AbstractString) = [ parse(Float64, x) for x in split(s, ",") ]

""" Parse Graphviz point.

http://www.graphviz.org/doc/info/attrs.html#k:point
"""
parse_point(s::AbstractString) = SVector{2}(parse_vector(s))

""" Parse Graphviz spline.

In Graphviz, a "spline" is a cubic B-spline of overlapping cubic Bezier curves.
It consists of 3n+1 points, where n is the number of Bezier curves.

http://www.graphviz.org/doc/info/attrs.html#k:splineType
https://web.archive.org/web/20170418034924/http://www.graphviz.org/content/how-convert-b-spline-bezier
"""
function parse_spline(spline::AbstractString)
  points = StaticVector{2,Float64}[]
  start, stop = nothing, nothing
  for s in split(spline, " ")
    if startswith(s, "s,"); start = parse_point(s[3:end])
    elseif startswith(s, "e,"); stop = parse_point(s[3:end])
    else push!(points, parse_point(s)) end
  end
  # Prefer explicit start or end points to the spline start and end points.
  # Thus, endpoints may pass into the node shape but should not fall short.
  if !isnothing(start); points[0] = start end
  if !isnothing(stop); points[end] = stop end
  points
end

""" Convert a property graph to a Graphviz graph.

This method is usually more convenient than direct AST manipulation for creating
Graphviz graphs. For more advanced features, like nested subgraphs, you must use
the Graphviz AST directly.
"""
function to_graphviz(g::AbstractPropertyGraph)::Graphviz.Graph
  gv_name(v::Int) = "n$v"
  gv_path(e::Int) = [gv_name(src(g,e)), gv_name(tgt(g,e))]

  # Add Graphviz node for each vertex in property graph.
  stmts = Graphviz.Statement[]
  for v in vertices(g)
    push!(stmts, Graphviz.Node(gv_name(v), vprops(g, v)))
  end

  # Add Graphviz edge for each edge in property graph.
  is_directed = !(g isa SymmetricPropertyGraph)
  for e in edges(g)
    # In undirected case, only include one edge from each pair.
    if is_directed || (e <= inv(g,e))
      push!(stmts, Graphviz.Edge(gv_path(e), eprops(g, e)))
    end
  end

  attrs = gprops(g)
  Graphviz.Graph(
    name = get(attrs, :name, "G"),
    directed = is_directed,
    prog = get(attrs, :prog, is_directed ? "dot" : "neato"),
    stmts = stmts,
    graph_attrs = Graphviz.as_attributes(get(attrs, :graph, Dict())),
    node_attrs = Graphviz.as_attributes(get(attrs, :node, Dict())),
    edge_attrs = Graphviz.as_attributes(get(attrs, :edge, Dict())),
  )
end

# Graphs
########

""" Convert a graph to a Graphviz graph.

A simple default style is applied. For more control over the visual appearance,
first convert the graph to a property graph, define the Graphviz attributes as
needed, and then convert to a Graphviz graph.
"""
function to_graphviz(g::AbstractGraph;
    prog::AbstractString="dot", graph_attrs::AbstractDict=Dict(),
    node_attrs::AbstractDict=Dict(), edge_attrs::AbstractDict=Dict(),
    node_labels::Bool=false, edge_labels::Bool=false)
  node_labeler(v) = Dict(:label => node_labels ? string(v) : "")
  edge_labeler(e) = if edge_labels
    Dict(:label => string(e))
  else
    Dict{Symbol,String}()
  end
  to_graphviz(PropertyGraph{Any}(g, node_labeler, edge_labeler;
    prog = prog,
    graph = merge(Dict(:rankdir => "LR"), graph_attrs),
    node = merge(Dict(
      :shape => node_labels ? "circle" : "point",
      :width => "0.05", :height => "0.05", :margin => "0",
    ), node_attrs),
    edge = merge(Dict(:arrowsize => "0.5"), edge_attrs),
  ))
end

# Symmetric graphs
##################

function to_graphviz(g::AbstractSymmetricGraph;
    prog::AbstractString="neato", graph_attrs::AbstractDict=Dict(),
    node_attrs::AbstractDict=Dict(), edge_attrs::AbstractDict=Dict(),
    node_labels::Bool=false, edge_labels::Bool=false)
  node_labeler(v) = Dict(:label => node_labels ? string(v) : "")
  edge_labeler(e) = if edge_labels
    e′ = inv(g,e)
    Dict(:label => "($(min(e,e′)),$(max(e,e′)))")
  else
    Dict{Symbol,String}()
  end
  to_graphviz(SymmetricPropertyGraph{Any}(g, node_labeler, edge_labeler;
    prog = prog,
    graph = graph_attrs,
    node = merge(Dict(
      :shape => node_labels ? "circle" : "point",
      :width => "0.05", :height => "0.05", :margin => "0",
    ), node_attrs),
    edge = merge(Dict(:len => "0.5"), edge_attrs),
  ))
end

# Half-edge graphs
##################

function to_graphviz(g::AbstractHalfEdgeGraph;
    prog::AbstractString="neato", graph_attrs::AbstractDict=Dict(),
    node_attrs::AbstractDict=Dict(), edge_attrs::AbstractDict=Dict(),
    node_labels::Bool=false, edge_labels::Bool=false)
  pg = SymmetricPropertyGraph{Any}(;
    prog = prog,
    graph = graph_attrs,
    node = merge(Dict(
      :shape => node_labels ? "circle" : "point",
      :width => "0.05", :height => "0.05", :margin => "0",
    ), node_attrs),
    edge = merge(Dict(:len => "0.5"), edge_attrs),
  )
  for v in vertices(g)
    add_vertex!(pg, label=node_labels ? string(v) : "")
  end
  for e in half_edges(g)
    e′ = inv(g,e)
    if e == e′
      # Dangling half-edge: add an invisible vertex.
      v = add_vertex!(pg, style="invis", shape="none", label="")
      new_edge = add_edge!(pg, vertex(g,e), v)
      if edge_labels
        set_eprop!(pg, new_edge, :label, string(e))
      end
    elseif e < e′
      # Pair of distict half-edges: add a standard edge.
      new_edge = add_edge!(pg, vertex(g,e), vertex(g,e′))
      if edge_labels
        set_eprop!(pg, new_edge, :label, "($e,$e′)")
      end
    end
  end
  to_graphviz(pg)
end

end
