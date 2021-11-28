module FinFunctors
export to_graphviz

using ...CategoricalAlgebra, ...CategoricalAlgebra.FreeDiagrams, ...CategoricalAlgebra.Diagrams, 
    ...Graphs, ..GraphvizGraphs
import ..Graphviz
import ..GraphvizGraphs: to_graphviz, to_graphviz_property_graph

function to_graph(J::FinCat)
    g = BasicGraphs.Graph()
    copy_parts!(g, graph(J))
    return g
end

to_graphviz(F::FinFunctor; kw...) =
to_graphviz(GraphvizGraphs.to_graphviz_property_graph(F; kw...))

function to_graphviz_property_graph(F::FinFunctor; kw...)
    J = dom(F)
    G = graph(J)
    pg = GraphvizGraphs.to_graphviz_property_graph(to_graph(J); kw...)
    for v in vertices(G)
        lᵥ = G[v, :vname]
        tᵥ = F.ob_map[v]
        set_vprops!(pg, v, Dict(:label => "$(lᵥ):$tᵥ"))
    end
    for e in edges(G)
        tₑ = F.hom_map[e]
        set_eprops!(pg, e, Dict(:label => "$tₑ"))
    end
    pg
end
end