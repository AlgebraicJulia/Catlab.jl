""" Graphviz drawing of categories, functors, diagrams, and related structures.
"""
module GraphvizCategories
export to_graphviz, to_graphviz_property_graph

using ...Theories, ...CategoricalAlgebra, ...Graphs, ...BasicSets, ..GraphvizGraphs
import ..Graphviz
import ..GraphvizGraphs: to_graphviz, to_graphviz_property_graph

# Presentations
###############

to_graphviz(pres::Presentation, args...; kw...) =
  to_graphviz(to_graphviz_property_graph(pres, args...; kw...))

function to_graphviz_property_graph(pres::Presentation, Ob::Symbol, Hom::Symbol;
    prog::AbstractString="neato", graph_attrs::AbstractDict=Dict(),
    node_attrs::AbstractDict=Dict(), edge_attrs::AbstractDict=Dict())
  pg = PropertyGraph{Any}(; prog = prog,
    graph = graph_attrs,
    node = merge!(Dict(:shape => "ellipse", :margin => "0"), node_attrs),
    edge = edge_attrs,
  )

  obs = generators(pres, Ob)
  add_vertices!(pg, length(obs))
  for (v, ob) in enumerate(obs)
    set_vprop!(pg, v, :label, string(first(ob)))
  end

  homs = generators(pres, Hom)
  add_edges!(pg, map(f -> generator_index(pres, first(gat_type_args(f))), homs),
                 map(f -> generator_index(pres, last(gat_type_args(f))), homs))
  for (e, hom) in enumerate(homs)
    set_eprop!(pg, e, :label, string(first(hom)))
  end
  pg
end

# Categories
############

function to_graphviz_property_graph(pres::Presentation{ThCategory.Meta.T}; kw...)
  to_graphviz_property_graph(pres, :Ob, :Hom; kw...)
end

function to_graphviz_property_graph(pres::Presentation{ThMCategory.Meta.T};
    tight_attrs::AbstractDict=Dict(:arrowhead => "empty"), kw...)
  pg = to_graphviz_property_graph(pres, :Ob, :Hom; kw...)
  for tight_hom in generators(pres, :Tight)
    e = generator_index(pres, hom(tight_hom))
    set_eprops!(pg, e, tight_attrs)
  end
  pg
end

to_graphviz(X::AbstractElements; kw...) =
  to_graphviz(to_graphviz_property_graph(X; kw...))

function to_graphviz_property_graph(X::AbstractElements;
    prog::AbstractString="neato", graph_attrs::AbstractDict=Dict(),
    node_attrs::AbstractDict=Dict(), edge_attrs::AbstractDict=Dict(),
    node_labels::Bool=false, edge_labels::Bool=false)
  pg = PropertyGraph{Any}(; prog = prog,
    graph = graph_attrs,
    node = merge!(Dict(:shape => "box", :width => "0", :height => "0",
                       :margin => "0.025"), node_attrs),
    edge = edge_attrs)

  add_vertices!(pg, nparts(X, :El))
  add_edges!(pg, X[:src], X[:tgt])

  for v in parts(X, :El)
    vlabel = X[X[v, :πₑ], :nameo]
    set_vprop!(pg, v, :label, node_labels ? "$v:$vlabel" : "$vlabel")
  end
  for e in parts(X, :Arr)
    elabel = X[X[e, :πₐ], :nameh]
    set_eprop!(pg, e, :label, edge_labels ? "$e:$elabel" : "$elabel")
  end
  pg
end

# Diagrams
##########

to_graphviz(d::FinDomFunctor; kw...) =
  to_graphviz(to_graphviz_property_graph(d; kw...))

function to_graphviz_property_graph(d::FinDomFunctor; kw...)
  lab = impl_type(dom(d), :Ob) == Symbol
  g = (lab ? NamedGraph : Graph)(dom(d))
  pg = to_graphviz_property_graph(g; kw...)
  for v in vertices(g)
    vname = vertex_name(g, v) 
    tᵥ = ob_map(d, lab ? vname : v)
    labels = lab ? [vname, tᵥ] : [tᵥ]
    set_vprop!(pg, v, :label, join(labels, ":"))
  end
  for e in edges(g)
    tₑ = gen_map(d, lab ? edge_name(g, e) : e)
    set_eprop!(pg, e, :label, string(tₑ))
  end
  pg
end

# Schemas
#########

function to_graphviz_property_graph(pres::Presentation{ThSchema.Meta.T}; kw...)
  pg = to_graphviz_property_graph(pres, :Ob, :Hom; kw...)
  ob_vertices = vertices(pg)
  hom_edges = edges(pg)

  attr_types = generators(pres, :AttrType)
  attr_vertices = add_vertices!(pg, length(attr_types))
  for (v, attr_type) in zip(attr_vertices, attr_types)
    set_vprops!(pg, v, xlabel=string(first(attr_type)), shape="point")
  end

  attrs = generators(pres, :Attr)
  attr_edges = add_edges!(pg,
    map(attr -> ob_vertices[generator_index(pres, dom(attr))], attrs),
    map(attr -> attr_vertices[generator_index(pres, codom(attr))], attrs))
  for (e, attr) in zip(attr_edges, attrs)
    set_eprop!(pg, e, :label, string(first(attr)))
  end
  pg
end

# Functions
###########

""" Visualize a function between finite sets using Graphviz.

Visualize a function (`FinFunction`) between two finite sets (`FinSet`s).
Reduces to drawing an undirected bipartite graph; see that method for more.
"""
function to_graphviz(f::FinFunction; kw...)
  g = UndirectedBipartiteGraph(length(dom(f)), length(codom(f)))
  for i in dom(f)
    add_edge!(g, i, f(i))
  end
  to_graphviz(g; kw...)
end

end # module
