""" Graphviz drawing of categories, functors, diagrams, and related structures.
"""
module GraphvizCategories
export to_graphviz

using ...CategoricalAlgebra, ...Graphs, ..GraphvizGraphs
import ..Graphviz
import ..GraphvizGraphs: to_graphviz, to_graphviz_property_graph

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

end
