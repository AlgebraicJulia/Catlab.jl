""" Graphviz support for Catlab's graph types.
"""
module GraphvizGraphs
export parse_graphviz, to_graphviz, to_graphviz_property_graph

using StaticArrays: StaticVector, SVector
using Colors: Colorant, @colorant_str, hex, distinguishable_colors

using ...Theories
using ...Graphs, ...CategoricalAlgebra.Subobjects, ...CategoricalAlgebra.CSets
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
    props[:size] = 72*SVector(parse(Float64, node["width"]),
                              parse(Float64, node["height"]))
    add_vertex!(graph, props)
  end

  # Add edge for each Graphviz edge.
  edge_keys = ("id", "comment", "label", "xlabel", "headlabel", "taillabel",
               "headport", "tailport")
  for edge in get(doc, "edges", ())
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
simple Graphviz graphs. For more advanced features, like nested subgraphs, you
must use the Graphviz AST.
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
    graph_attrs = get(attrs, :graph, Dict()),
    node_attrs = get(attrs, :node, Dict()),
    edge_attrs = get(attrs, :edge, Dict()),
  )
end

# Graphs
########

""" Convert a graph to a Graphviz graph.

A simple default style is applied. For more control over the visual appearance,
first convert the graph to a property graph, define the Graphviz attributes as
needed, and finally convert the property graph to a Graphviz graph.
"""
function to_graphviz(g::HasGraph; kw...)
  to_graphviz(to_graphviz_property_graph(g; kw...))
end

""" Convert graph or other structure to a property graph suitable for Graphviz.

This function is an intermediate step in many methods of the generic function
[`to_graphviz`](@ref), but can be useful in its own right for customizing the
Graphviz graph beyond whatever options are supported by [`to_graphviz`](@ref).
"""
function to_graphviz_property_graph(g::AbstractGraph;
    prog::AbstractString="dot", graph_attrs::AbstractDict=Dict(),
    node_attrs::AbstractDict=Dict(), edge_attrs::AbstractDict=Dict(),
    node_labels::Union{Symbol,Bool}=false, edge_labels::Union{Symbol,Bool}=false)
  PropertyGraph{Any}(g, v -> node_label(g, node_labels, v),
                     e -> edge_label(g, edge_labels, e);
    prog = prog,
    graph = merge!(default_graph_attrs(prog), graph_attrs),
    node = merge!(default_node_attrs(node_labels), node_attrs),
    edge = merge!(default_edge_attrs(prog), edge_attrs),
  )
end

node_label(g, name::Symbol, v::Int) = Dict(:label => string(g[v, name]))
node_label(g, labels::Bool, v::Int) = Dict(:label => labels ? string(v) : "")

edge_label(g, name::Symbol, e::Int) = Dict(:label => string(g[e, name]))
edge_label(g, labels::Bool, e::Int) =
  labels ? Dict(:label => string(e)) : Dict{Symbol,String}()

function default_graph_attrs(prog::AbstractString)
  attrs = Dict{Symbol,String}()
  prog == "dot" && (attrs[:rankdir] = "LR")
  attrs
end

function default_node_attrs(labels::Union{Symbol,Bool})
  shape = labels isa Symbol ? "ellipse" : (labels ? "circle" : "point")
  Dict(:shape => shape, :width => "0.05", :height => "0.05", :margin => "0")
end

function default_edge_attrs(prog::AbstractString)
  attrs = Dict(:arrowsize => "0.5")
  prog ∈ ("neato", "fdp") && (attrs[:len] = "0.5")
  attrs
end

# Symmetric graphs
##################

function to_graphviz_property_graph(g::AbstractSymmetricGraph;
    prog::AbstractString="neato", graph_attrs::AbstractDict=Dict(),
    node_attrs::AbstractDict=Dict(), edge_attrs::AbstractDict=Dict(),
    node_labels::Union{Symbol,Bool}=false, edge_labels::Union{Symbol,Bool}=false)
  SymmetricPropertyGraph{Any}(g, v -> node_label(g, node_labels, v),
                              e -> symmetric_edge_label(g, edge_labels, e);
    prog = prog,
    graph = merge!(default_graph_attrs(prog), graph_attrs),
    node = merge!(default_node_attrs(node_labels), node_attrs),
    edge = merge!(default_edge_attrs(prog), edge_attrs),
  )
end

symmetric_edge_label(g, name::Symbol, e::Int) = edge_label(g, name, e)

function symmetric_edge_label(g, labels::Bool, e::Int)
  if labels
    e′ = inv(g,e)
    Dict(:label => (e == e′ ? string(e) : "($(min(e,e′)),$(max(e,e′)))"))
  else
    Dict{Symbol,String}()
  end
end

# Reflexive graphs
##################

function to_graphviz_property_graph(g::AbstractReflexiveGraph;
    prog::AbstractString="dot", graph_attrs::AbstractDict=Dict(),
    node_attrs::AbstractDict=Dict(), edge_attrs::AbstractDict=Dict(),
    node_labels::Union{Symbol,Bool}=false, edge_labels::Union{Symbol,Bool}=false,
    show_reflexive::Bool=false)
  pg = PropertyGraph{Any}(; prog = prog,
    graph = merge!(default_graph_attrs(prog), graph_attrs),
    node = merge!(default_node_attrs(node_labels), node_attrs),
    edge = merge!(default_edge_attrs(prog), edge_attrs),
  )
  add_vertices!(pg, nv(g))
  for v in vertices(g)
    set_vprops!(pg, v, node_label(g, node_labels, v))
  end
  reflexive_edges = Set(refl(g))
  for e in edges(g)
    is_reflexive = e ∈ reflexive_edges
    if show_reflexive || !is_reflexive
      e′ = add_edge!(pg, src(g,e), tgt(g,e))
      is_reflexive && set_eprop!(pg, e′, :style, "dashed")
      set_eprops!(pg, e′, edge_label(g, edge_labels, e))
    end
  end
  pg
end

# Symmetric reflexive graphs
############################

function to_graphviz_property_graph(g::AbstractSymmetricReflexiveGraph;
    prog::AbstractString="neato", graph_attrs::AbstractDict=Dict(),
    node_attrs::AbstractDict=Dict(), edge_attrs::AbstractDict=Dict(),
    node_labels::Union{Symbol,Bool}=false, edge_labels::Union{Symbol,Bool}=false,
    show_reflexive::Bool=false)
  pg = SymmetricPropertyGraph{Any}(; prog = prog,
    graph = merge!(default_graph_attrs(prog), graph_attrs),
    node = merge!(default_node_attrs(node_labels), node_attrs),
    edge = merge!(default_edge_attrs(prog), edge_attrs),
  )
  add_vertices!(pg, nv(g))
  for v in vertices(g)
    set_vprops!(pg, v, node_label(g, node_labels, v))
  end
  reflexive_edges = Set(refl(g))
  for e in edges(g)
    is_reflexive = e ∈ reflexive_edges
    if (is_reflexive ? show_reflexive : e <= inv(g,e))
      e′ = first(add_edge!(pg, src(g,e), tgt(g,e)))
      is_reflexive && set_eprop!(pg, e′, :style, "dashed")
      set_eprops!(pg, e′, symmetric_edge_label(g, edge_labels, e))
    end
  end
  pg
end

# Half-edge graphs
##################

to_graphviz(g::AbstractHalfEdgeGraph; kw...) =
  to_graphviz(to_graphviz_property_graph(g; kw...))

function to_graphviz_property_graph(g::AbstractHalfEdgeGraph;
    prog::AbstractString="neato", graph_attrs::AbstractDict=Dict(),
    node_attrs::AbstractDict=Dict(), edge_attrs::AbstractDict=Dict(),
    node_labels::Union{Symbol,Bool}=false, edge_labels::Union{Symbol,Bool}=false)
  pg = SymmetricPropertyGraph{Any}(; prog = prog,
    graph = merge!(default_graph_attrs(prog), graph_attrs),
    node = merge!(default_node_attrs(node_labels), node_attrs),
    edge = merge!(default_edge_attrs(prog), edge_attrs),
  )
  for v in vertices(g)
    add_vertex!(pg, label=node_labels ? string(v) : "")
  end
  for e in half_edges(g)
    if e == inv(g,e)
      # Dangling half-edge: add an invisible vertex.
      v = add_vertex!(pg, style="invis", shape="none", label="")
      e′ = first(add_edge!(pg, vertex(g,e), v))
      set_eprops!(pg, e′, symmetric_edge_label(g, edge_labels, e))
    elseif e < inv(g,e)
      # Pair of distict half-edges: add a standard edge.
      e′ = first(add_edge!(pg, vertex(g,e), vertex(g,inv(g,e))))
      set_eprops!(pg, e′, symmetric_edge_label(g, edge_labels, e))
    end
  end
  pg
end

# Subgraphs
###########

to_graphviz(subgraph::Subobject{<:HasGraph}; kw...) =
  to_graphviz(to_graphviz_property_graph(subgraph; kw...))

function to_graphviz_property_graph(
    subgraph::Subobject{<:Union{AbstractGraph,AbstractSymmetricGraph}};
    subgraph_node_attrs::AbstractDict=default_subgraph_node_attrs,
    subgraph_edge_attrs::AbstractDict=default_subgraph_edge_attrs, kw...)
  pg = to_graphviz_property_graph(ob(subgraph); kw...)
  f = hom(subgraph)
  for v in vertices(dom(f))
    set_vprops!(pg, f[:V](v), subgraph_node_attrs)
  end
  for e in edges(dom(f))
    set_eprops!(pg, f[:E](e), subgraph_edge_attrs)
  end
  pg
end

const default_subgraph_node_attrs = Dict(:color => "cornflowerblue")
const default_subgraph_edge_attrs = Dict(:color => "cornflowerblue")

# Graph homomorphisms
#####################

""" Visualize a graph homomorphism using Graphviz.

Visualize a homomorphism (`ACSetTransformation`) between two graphs (instances
of `AbstractGraph`). By default, the domain and codomain are drawn as subgraphs
and the vertex mapping is drawn using dotted edges, whereas the edge map is
suppressed. The vertex and edge mapping can also be shown using colors, via the
`node_colors` and `edge_colors` keyword arguments.

# Arguments
- `draw_codom=true`: whether to draw the codomain graph
- `draw_mapping=true`: whether to draw the vertex mapping using edges
- `prog="dot"`: Graphviz program to use
- `graph_attrs`: Graph-level Graphviz attributes
- `node_attrs`: Node-level Graphviz attributes
- `edge_attrs`: Edge-level Graphviz attributes
- `node_labels=false`: whether to draw node labels and which vertex attribute to use
- `edge_labels=false`: whether to draw edge labels and which edge attribute to use
- `node_colors=!draw_codom`: whether and how to color nodes based on vertex map
- `edge_colors=!draw_codom`: whether and how to color edges based on edge map
"""
function to_graphviz(f::ACSetTransformation{S,Comp,<:AbstractGraph,<:AbstractGraph};
    draw_codom::Bool=true, draw_mapping::Bool=true,
    prog::AbstractString="dot", graph_attrs::AbstractDict=Dict(),
    node_attrs::AbstractDict=Dict(), edge_attrs::AbstractDict=Dict(),
    node_labels::Union{Symbol,Bool}=false, edge_labels::Union{Symbol,Bool}=false,
    node_colors::Union{Nothing,Bool}=nothing,
    edge_colors::Union{Nothing,Bool}=nothing) where {S,Comp}
  stmts = Graphviz.Statement[]
  g, h = dom(f), codom(f)

  # mapping between edges and between vertices given by colors
  isnothing(node_colors) && (node_colors = !draw_codom)
  isnothing(edge_colors) && (edge_colors = !draw_codom)
  node_colors == true && (node_colors = default_node_colors)
  edge_colors == true && (edge_colors = default_edge_colors)
  vcolors = node_colors != false ? node_colors(nv(h)) : nothing
  ecolors = edge_colors != false ? edge_colors(ne(h)) : nothing

  # subgraph for g = dom(f)
  dom_nodes = map(vertices(g)) do v
    Graphviz.Node("dom_$v", merge!(node_color(vcolors, f[:V](v)),
                                   node_label(g, node_labels, v)))
  end
  dom_edges = map(edges(g)) do e
    Graphviz.Edge(["dom_$(src(g,e))", "dom_$(tgt(g,e))"],
                  merge!(edge_color(ecolors, f[:E](e)),
                         edge_label(g, edge_labels, e)))
  end
  dom_stmts = vcat(dom_nodes, dom_edges)
  if draw_codom && nv(g) > 0
    push!(stmts, Graphviz.Subgraph("cluster_dom", dom_stmts))
  else
    append!(stmts, dom_stmts)
  end

  # subgraph for h = codom(f)
  if draw_codom
    codom_nodes = map(vertices(h)) do v
      Graphviz.Node("cod_$v", merge!(node_color(vcolors, v),
                                     node_label(h, node_labels, v)))
    end
    codom_edges = map(edges(h)) do e
      Graphviz.Edge(["cod_$(src(h,e))", "cod_$(tgt(h,e))"],
                    merge!(edge_color(ecolors, e),
                           edge_label(h, edge_labels, e)))
    end
    codom_stmts = vcat(codom_nodes, codom_edges)
    push!(stmts, Graphviz.Subgraph("cluster_cod", codom_stmts))
  end

  # mapping between vertices
  if draw_codom && draw_mapping
    map_stmts = map(vertices(g)) do v
      Graphviz.Edge(["\"dom_$v\"", "\"cod_$(f[:V](v))\""], Graphviz.Attributes(
        :constraint => "false", :style => "dotted"))
    end
    append!(stmts, map_stmts)
  end

  Graphviz.Digraph("hom_graph", stmts, prog=prog,
    graph_attrs = merge!(default_graph_attrs(prog), graph_attrs),
    node_attrs = merge!(default_node_attrs(node_labels), node_attrs),
    edge_attrs = merge!(default_edge_attrs(prog), edge_attrs))
end

function node_color(colors::AbstractVector{<:Colorant}, v::Int)
  Dict(:color => string("#", hex(colors[v])))
end
node_color(::Nothing, v::Int) = Dict{Symbol,String}()

function edge_color(colors::AbstractVector{<:Colorant}, e::Int)
  Dict(:color => string("#", hex(colors[e])))
end
edge_color(::Nothing, e::Int) = Dict{Symbol,String}()

function default_node_colors(n)
  distinguishable_colors(n, [colorant"white", colorant"black"], dropseed=true)
end
function default_edge_colors(n)
  distinguishable_colors(n, colorant"#F8766D", lchoices=[65], cchoices=[100])
end

end
