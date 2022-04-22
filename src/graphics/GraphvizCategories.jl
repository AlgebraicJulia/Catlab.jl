""" Graphviz drawing of categories, functors, diagrams, and related structures.
"""
module GraphvizCategories
export to_graphviz

using ...Present, ...Theories
using ...CategoricalAlgebra, ...Graphs, ..GraphvizGraphs
import ..Graphviz
import ..GraphvizGraphs: to_graphviz, to_graphviz_property_graph

# Diagrams
##########

function to_graphviz(F::FinFunctor; kw...)
  to_graphviz(to_graphviz_property_graph(F; kw...))
end

function to_graphviz_property_graph(F::FinFunctor; kw...)
  g = graph(dom(F))
  pg = to_graphviz_property_graph(g; kw...)
  for v in vertices(g)
    lᵥ = g[v, :vname]
    tᵥ = ob_map(F, v)
    set_vprop!(pg, v, :label, string(lᵥ, ":", tᵥ))
  end
  for e in edges(g)
    tₑ = hom_map(F, e)
    set_eprop!(pg, e, :label, string(tₑ))
  end
  pg
end

# Schemas
#########

to_graphviz(pres::Presentation{Schema}; kw...) =
  to_graphviz(to_graphviz_property_graph(pres; kw...))

function to_graphviz_property_graph(pres::Presentation{Schema};
    prog::AbstractString="neato", graph_attrs::AbstractDict=Dict(),
    node_attrs::AbstractDict=Dict(), edge_attrs::AbstractDict=Dict())
  pg = PropertyGraph{Any}(; prog = prog,
    graph = graph_attrs,
    node = merge!(Dict(:margin => "0"), node_attrs),
    edge = merge!(Dict(:len => "1.5"), edge_attrs),
  )

  obs = generators(pres, :Ob)
  ob_vertices = add_vertices!(pg, length(obs))
  for (v, ob) in zip(ob_vertices, obs)
    set_vprops!(pg, v, label=string(first(ob)), shape="circle")
  end

  attr_types = generators(pres, :AttrType)
  attr_vertices = add_vertices!(pg, length(attr_types))
  for (v, attr_type) in zip(attr_vertices, attr_types)
    set_vprops!(pg, v, xlabel=string(first(attr_type)), shape="point")
  end

  homs = generators(pres, :Hom)
  hom_edges = add_edges!(pg,
    ob_vertices[generator_index.(Ref(pres), first.(dom.(homs)))],
    ob_vertices[generator_index.(Ref(pres), first.(codom.(homs)))])
  for (e, hom) in zip(hom_edges, homs)
    set_eprop!(pg, e, :label, string(first(hom)))
  end

  attrs = generators(pres, :Attr)
  attr_edges = add_edges!(pg,
    ob_vertices[generator_index.(Ref(pres), first.(dom.(attrs)))],
    attr_vertices[generator_index.(Ref(pres), first.(codom.(attrs)))])
  for (e, attr) in zip(attr_edges, attrs)
    set_eprop!(pg, e, :label, string(first(attr)))
  end

  pg
end

end
