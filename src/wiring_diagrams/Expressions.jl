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
using ...Doctrines: CategoryExpr, ObExpr, HomExpr, id, compose, otimes, munit
using ..WiringDiagramCore, ..WiringLayers

# Expression -> Diagram
#######################

""" Convert a morphism expression into a wiring diagram.

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

""" Convert a wiring diagram into a morphism expression.

The boxes are assumed to carry morphism expressions (`HomExpr`) and the ports to
carry object expressions (`ObExpr`).
"""
function to_hom_expr(d::WiringDiagram)::HomExpr
  n = nboxes(d)
  while true
    # Parallel reduction.
    # TODO
    
    # Series reduction.
    series = series_in_graph(graph(d))
    composites = HomExpr[]
    for vs in series
      exprs = HomExpr[ box(d,vs[1]).value ]
      for i in 2:length(vs)
        layer = wiring_layer_between(diagram, vs[i-1], vs[i])
        layer_expr = to_hom_expr(
          layer, output_ports(d, vs[i-1]), input_ports(d, vs[i]))
        append!(exprs, [layer_expr, box(d,vs[i]).value])
      end
      push!(composites, compose(expr))
    end
    if !isempty(series)
      encapsulate!(d, series, discard_boxes=true, values=composites)
    end
    
    # Repeat until the box count stops decreasing.
    nboxes(d) >= n && break
    n = nboxes(d)
  end
end

""" Find parallel compositions in a graph.
"""
function parallel_in_graph(g::DiGraph)::Dict{Pair{Int,Int},Vector{Int}}
  parallel = Dict{Pair{Int,Int},Vector{Int}}()
  for v in 1:nv(g)
    if length(inneighbors(g,v)) == 1 && length(outneighbors(g,v)) == 1
      src, tgt = first(inneighbors(g,v)), first(outneighbors(g,v))
      push!(get!(parallel, src => tgt, Int[]), v)
    end
  end
  filter(pair -> length(last(pair)) > 1, parallel)
end

""" Find series compositions in a graph.
"""
function series_in_graph(g::DiGraph)::Vector{Vector{Int}}
  reduced = DiGraph(nv(g))
  for edge in edges(g)
    if (length(outneighbors(g,src(edge))) == 1 &&
        length(inneighbors(g,dst(edge))) == 1)
      add_edge!(reduced, edge)
    end
  end
  series = Vector{Int}[]
  for component in weakly_connected_components(reduced)
    if length(component) > 1
      sub, vmap = induced_subgraph(reduced, component)
      push!(series, Int[ vmap[v] for v in topological_sort_by_dfs(sub) ])
    end
  end
  series
end

# Layer -> Expression
#####################

""" Convert a wiring layer into a morphism expression.
"""
function to_hom_expr(layer::WiringLayer, inputs::Vector, outputs::Vector)
  σ = to_permutation(layer)
  @assert !isnothing(σ) "Conversion of non-permutation not implemented"
  @assert inputs == outputs
  permutation_to_hom_expr(layer, inputs)
end

""" Convert a typed permutation into a morphism expression.
"""
function permutation_to_hom_expr(σ::Vector{Int}, types::Vector)
  @assert all(σ[i] == i for i in eachindex(σ)) "Conversion of non-identity not implemented"
  id(otimes(types))
end

""" Convert a wiring layer into a permutation, if it is one.

Otherwise, return nothing.
"""
function to_permutation(layer::WiringLayer)::Union{Nothing,Vector{Int}}
  nin, nout = layer.ninputs, layer.noutputs
  if nin != nout; return nothing end
  σ = zeros(Int, nin)
  for i in 1:nin
    wires = out_wires(layer, i)
    if length(wires) == 1
      σ[i] = last(first(wires))
    else
      return nothing
    end
  end
  return σ
end

end
