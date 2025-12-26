module Visualization
export graphviz, view_window

using Blink
using Interact
using AlgebraicRewriting
using Catlab.CategoricalAlgebra

using Catlab.Graphs
using Catlab.Graphics.Graphviz: Statement
import Catlab.Graphics: to_graphviz, to_graphviz_property_graph
import Catlab.Graphics.GraphvizGraphs: node_label, default_node_attrs
import Catlab.Graphics.Graphviz: pprint
import Catlab.Graphics.Graphviz
import Catlab.Graphics: to_graphviz

using AlgebraicRewriting
using ..Setup

struct Title <: Statement
  title::String
end

function pprint(io, titl::Title, n::Int; directed::Bool=false)
  print(io, """labelloc="t";
  label="$(titl.title)";""")
end

function to_graphviz(g::AbstractPropertyGraph)::Graphviz.Graph
  gv_name(v::Int) = "n$v"
  gv_path(e::Int) = [gv_name(src(g,e)), gv_name(tgt(g,e))]

  # Add Graphviz node for each vertex in property graph.

  stmts = Graphviz.Statement[gprops(g)[:stmts]...]

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
  ga = Graphviz.as_attributes(get(attrs, :graph, Dict()))
  na = Graphviz.as_attributes(get(attrs, :node, Dict()))
  ea = Graphviz.as_attributes(get(attrs, :edge, Dict()))
  Graphviz.Graph(
    name = get(attrs, :name, "G"),
    directed = is_directed,
    prog = get(attrs, :prog, is_directed ? "dot" : "neato"),
    stmts = stmts,
    graph_attrs = ga,
    node_attrs = na,
    edge_attrs = ea,
  )
end
function to_graphviz_property_graph(g::AbstractGraph;
  prog::AbstractString="dot", graph_attrs::AbstractDict=Dict(),
  node_attrs::AbstractDict=Dict(), edge_attrs::AbstractDict=Dict(),
  node_labels::Union{Symbol,Bool, Pair{Symbol, <:Function}}=false,
  edge_labels::Union{Symbol,Bool, Pair{Symbol, <:Function}}=false,
  title::Union{Nothing, String} = nothing
  )
  grph = merge!(Dict{Any,Any}(:rankdir => "LR",), graph_attrs)
  nde = merge!(Dict{Any,Any}(default_node_attrs(node_labels)),
                             filter(x->!(x[2] isa AbstractVector), node_attrs))

  edg = merge!(Dict{Any,Any}(:arrowsize => "0.5"),
                             filter(x->!(x[2] isa AbstractVector),edge_attrs))
  pg = PropertyGraph{Any}(
    g,
    v -> node_label(g, node_labels, v),
    e -> edge_label(g, edge_labels, e);
    prog = prog,
    graph = grph,
    stmts= [Title(isnothing(title) ? "" : title)],
    node = nde,
    edge = edg,
  )
for (prop, vec) in filter(x->x[2] isa AbstractVector, node_attrs)
  length(vec) == nv(g) || error("Bad node attr vector length for prop $prop: $(length(vec))!=$(nv(g))")
  for (v,val) in zip(vertices(g), vec)
    set_vprops!(pg, v, Dict([prop=>string(val)]))
  end
end
for (prop, vec) in filter(x->x[2] isa AbstractVector, edge_attrs)
  length(vec) == ne(g) || error("Bad edge attr vector length for prop $prop")
  for (e,val) in zip(edges(g), vec)
    set_eprops!(pg, e, Dict([prop=>string(val)]))
  end
end

return pg
end
node_label(g, labels::Bool, v::Int) = labels ? Dict(:label => string(v)) : Dict{Symbol,String}()
node_label(g, namef::Pair{Symbol, <:Function}, e::Int) = node_label(g, namef[1], namef[2], e)
node_label(g, name::Symbol, f::Function, e::Int) = begin
lab = string(f(g[e, name]))
return lab == "" ? Dict() :  Dict(:label => lab, :shape=>"circle")
end

edge_label(g, labels::Bool, v::Int) = labels ? Dict(:label => string(v)) : Dict{Symbol,String}()
edge_label(g, namef::Pair{Symbol, <:Function}, e::Int) = edge_label(g, namef[1], namef[2], e)
edge_label(g, name::Symbol, f::Function, e::Int) = Dict(:label => string(f(g[e, name])))
function default_node_attrs(labels::Union{Symbol,Bool, Pair{Symbol, <:Function}})
  shape = labels isa Symbol ? "ellipse" : "point" #((!(labels isa Bool) || labels) ? "circle" : "point")
  Dict(:shape => shape, :width => "0.05", :height => "0.05", :margin => "0")
end



function graphviz(G::BW, pos=nothing; title=nothing)
  G = deepcopy(G)
  fc = Any[(!(c isa Bool) || c) ? "white" : "black" for c in G[:color]]
  n_v, n_e, ni, no = [nparts(G,x) for x in [:V,:E,:I,:O]]
  if !isnothing(pos)
    if length(pos) == n_v
      append!(pos, fill("", ni+no))
    elseif length(pos)!=n_v+ni+no
       error("pos $pos not length $n_v nor $(n_v+ni+no)")
    end
  end
  append!(fc, fill(:red, ni), fill(:blue, no))
  add_parts!(G,:V,ni+no; color=true)
  add_parts!(G,:E, ni+no; src=vcat(n_v+1:n_v+ni, G[:o]),
              tgt=vcat(G[:i],n_v+ni+1:nv(G)), weight=1//1)
  sty = vcat(fill("filled", n_v), fill("dotted", ni+no)) # why doesn't this work?
  n_a = Dict([:width=>".2", :height=>".2", :penwidth=>"3", :fillcolor=>fc,
              :style=>sty, :color=>"black"])
  if !isnothing(pos)
    n_a[:pos] = pos
  end
  esty = vcat(fill("solid", n_e), fill("dotted", ni+no))
  edir = vcat(fill("forward", n_e+ni), fill("forward", no)) # CHANGED
  e_a = Dict([:style=>esty, :dir=>edir])
  to_graphviz(G, title=title, prog=isnothing(pos) ? "dot" : "neato", node_attrs=n_a, edge_attrs=e_a,
            edge_labels= :weight => (x -> x == 1 ? "" : x),
            node_labels=:color => (x -> (x isa Var || x isa Expr) ? string(x) : ""))
end;

function view_window(x,y; positions=nothing)
  w = Window()
  body!(w, view_traj(x,y; positions=positions))
end

end # module
