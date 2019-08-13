""" Convert wiring diagrams to and from syntactic expressions.

Wiring diagrams are a graphical syntax for morphisms in a monoidal category. As
mathematical objects, they are intermediate between the morphisms themselves and
expressions in the textual syntax: a single morphism may correspond to many
wiring diagrams, and a single wiring diagram may correspond to many syntactic
expressions.

It is trivial to convert a morphism expression to a wiring diagram, but not to
go the other way around.
"""
module WiringDiagramExpressions
export to_hom_expr, to_wiring_diagram

using LightGraphs

using ...Syntax
using ...Doctrines: CategoryExpr, ObExpr, HomExpr
using ..WiringDiagramCore

# Expression -> Diagram
#######################

""" Convert a syntactic expression into a wiring diagram.

The morphism expression should belong to the doctrine of symmetric monoidal
categories, possibly with diagonals and codiagonals. Thus, the doctrines of
cartesian, cocartesian, and biproduct categories are supported.
"""
function to_wiring_diagram(expr::CategoryExpr)
  functor((Ports, WiringDiagram), expr;
    terms = Dict(
      :Ob => expr -> Ports([first(expr)]),
      :Hom => expr -> WiringDiagram(expr),
    )
  )
end

# Diagram -> Expression
#######################

""" Convert a wiring diagram to a syntactic expression.

The boxes are assumed to carry morphism expressions (`HomExpr`) and the ports to
carry object expressions (`ObExpr`).
"""
function to_hom_expr(diagram::WiringDiagram)::HomExpr
  # TODO
end

""" Find series compositions in a graph.
"""
function series_in_graph(g::DiGraph)::Set{Vector{Int}}
  reduced = DiGraph(nv(g))
  for edge in edges(g)
    if (length(outneighbors(g,src(edge))) == 1 &&
        length(inneighbors(g,dst(edge))) == 1)
      add_edge!(reduced, edge)
    end
  end
  series = Set{Vector{Int}}()
  for component in weakly_connected_components(reduced)
    if length(component) > 1
      sub, vmap = induced_subgraph(reduced, component)
      push!(series, Int[ vmap[v] for v in topological_sort_by_dfs(sub) ])
    end
  end
  series
end

end
