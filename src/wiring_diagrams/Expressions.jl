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
export to_ob_expr, to_hom_expr, to_wiring_diagram

using Compat
using LightGraphs

using ...Syntax, ...Doctrines
using ...Syntax: syntax_module
using ...Doctrines.Permutations
using ..WiringDiagramCore, ..WiringLayers, ..AlgebraicWiringDiagrams
import ..WiringLayers: to_wiring_diagram
using ..WiringDiagramAlgorithms: crossing_minimization_by_sort

# Expression -> Diagram
#######################

""" Convert a morphism expression into a wiring diagram.
"""
function to_wiring_diagram(expr::GATExpr, args...)
  theory = syntax_module(expr).theory()
  to_wiring_diagram(theory.Hom, expr, args...)
end
function to_wiring_diagram(T::Type, expr::GATExpr)
  to_wiring_diagram(T, expr, first, first)
end
function to_wiring_diagram(T::Type, expr::GATExpr, ob_map, hom_map)
  functor((Ports, WiringDiagram), expr; terms=Dict(
    :Ob => expr -> Ports{T}([ob_map(expr)]),
    :Hom => expr -> singleton_diagram(T,
      Box(hom_map(expr),
          to_wiring_diagram(T, dom(expr), ob_map, hom_map),
          to_wiring_diagram(T, codom(expr), ob_map, hom_map)))
  ))
end

# Diagram -> Expression
#######################

""" Convert a wiring diagram into a morphism expression.
"""
function to_hom_expr(Ob::Type, Hom::Type, d::WiringDiagram)
  box_to_expr(v::Int) = to_hom_expr(Ob, Hom, box(d,v))

  # Initial reduction: Add junction nodes to ensure any wiring layer between two
  # boxes is a permutation.
  d = add_junctions(d)

  # Dispatch special case: no boxes.
  if nboxes(d) == 0
    return hom_expr_between(Ob, d, input_id(d), output_id(d))
  end

  # Main loop: reduce until no further reduction is possible.
  n, changed = nboxes(d), true
  while changed
    # Transtive reduction: can only increase box count.
    d = transitive_reduction!(Ob, d)
    n, changed = nboxes(d), false
    while true
      # Alternating series/parallel reduction: can only decrease box count.
      d = series_reduction(Ob, Hom, d)
      d = parallel_reduction(Ob, Hom, d)
      d = input_parallel_reduction(Ob, Hom, d)
      d = output_parallel_reduction(Ob, Hom, d)
      nboxes(d) == n && break
      n, changed = nboxes(d), true
    end
  end

  # Termination: process all remaining boxes (always at least one, and exactly
  # one if there is no creation or deletion).
  if nboxes(d) > 1
    @assert all((wire.source.box == input_id(d) ||
                 wire.target.box == output_id(d)) for wire in wires(d))
    d = encapsulate_parallel(Ob, Hom, d,
      [(box_ids(d), [input_id(d)], [output_id(d)])])
  end
  v = first(box_ids(d))
  foldl(compose_simplify_id, [
    hom_expr_between(Ob, d, input_id(d), v),
    box_to_expr(v),
    hom_expr_between(Ob, d, v, output_id(d)),
  ])
end
function to_hom_expr(Syntax::Module, d::WiringDiagram)
  to_hom_expr(Syntax.Ob, Syntax.Hom, d)
end

to_hom_expr(::Type{Ob}, ::Type{Hom}, box::Box{<:Hom}) where {Ob,Hom} = box.value

function to_hom_expr(Ob::Type, Hom::Type, box::Box)
  dom = otimes(to_ob_exprs(Ob, input_ports(box)))
  codom = otimes(to_ob_exprs(Ob, output_ports(box)))
  Hom(box.value, dom, codom)
end
function to_hom_expr(Ob::Type, Hom::Type, op::BoxOp)
  invoke_term(parentmodule(Hom), head(op), to_hom_expr(Ob, Hom, op.box))
end
function to_hom_expr(Ob::Type, Hom::Type, junction::Junction)
  junction_to_expr(Ob, junction)
end

""" All possible parallel reductions of a wiring diagram.
"""
function parallel_reduction(Ob::Type, Hom::Type, d::WiringDiagram)
  parallel = find_parallel(graph(d), skip=outer_ids(d))
  encapsulate_parallel(Ob, Hom, d, [
    (vs, [src], [tgt]) for ((src, tgt), vs) in parallel
  ])
end

""" Input-sided parallel reduction of a wiring diagram.

Because these reductions are not necessarily unique, only one is performed,
the first one in topological sort order.
"""
function input_parallel_reduction(Ob::Type, Hom::Type, d::WiringDiagram)
  parallel = find_one_sided_parallel(graph(d), input=true, skip=outer_ids(d))
  if isempty(parallel); return d end
  sub, vmap = induced_subgraph(graph(d), collect(keys(parallel)))
  src = vmap[first(topological_sort_by_dfs(sub))]
  encapsulate_parallel(Ob, Hom, d, [ (parallel[src], [src], Int[]) ])
end

""" Output-sided parallel reduction of a wiring diagram.

Because these reductions are not necessarily unique, only one is performed,
the last one in topological sort order.
"""
function output_parallel_reduction(Ob::Type, Hom::Type, d::WiringDiagram)
  parallel = find_one_sided_parallel(graph(d), input=false, skip=outer_ids(d))
  if isempty(parallel); return d end
  sub, vmap = induced_subgraph(graph(d), collect(keys(parallel)))
  tgt = vmap[last(topological_sort_by_dfs(sub))]
  encapsulate_parallel(Ob, Hom, d, [ (parallel[tgt], Int[], [tgt]) ])
end

function encapsulate_parallel(Ob::Type, Hom::Type, d::WiringDiagram, parallel)
  parallel = Vector{Int}[
    vs[crossing_minimization_by_sort(d, vs, sources=sources, targets=targets)]
    for (vs, sources, targets) in parallel
  ]
  products = map(parallel) do vs
    exprs = Hom[ to_hom_expr(Ob, Hom, box(d,v)) for v in vs ]
    otimes(exprs)
  end
  encapsulate(d, parallel, discard_boxes=true, values=products)
end

""" All possible series reductions of a wiring diagram.
"""
function series_reduction(Ob::Type, Hom::Type, d::WiringDiagram)
  box_to_expr(v::Int) = to_hom_expr(Ob, Hom, box(d,v))

  series = find_series(graph(d), source=input_id(d), sink=output_id(d))
  composites = map(series) do vs
    exprs = Hom[ box_to_expr(vs[1]) ]
    for i in 2:length(vs)
      layer_expr = hom_expr_between(Ob, d, vs[i-1], vs[i])
      append!(exprs, [layer_expr, box_to_expr(vs[i])])
    end
    foldl(compose_simplify_id, exprs)
  end
  encapsulate(d, series, discard_boxes=true, values=composites)
end

""" All possible transitive reductions of a wiring diagram.
"""
function transitive_reduction!(Ob::Type, d::WiringDiagram)
  # Compute transitive reduction of underlying graph.
  # First add extra edges for the "invisible wires" corresponding to monoidal
  # units, since transitive reduction can be needed even in this case.
  reduced = copy(graph(d))
  for v in box_ids(d)
    if isempty(input_ports(d, v))
      add_edge!(reduced, input_id(d), v)
    end
    if isempty(output_ports(d, v))
      add_edge!(reduced, v, output_id(d))
    end
  end
  reduced = transitive_reduction!(reduced)

  # Add junction node for each wire removed by transitive reduction.
  for edge in collect(edges(graph(d)))
    if !has_edge(reduced, edge)
      for wire in wires(d, edge)
        value = port_value(d, wire.source) # =?= port_value(d, wire.target)
        v = add_box!(d, Junction(value, 1, 1))
        add_wire!(d, Wire(wire.source => Port(v,InputPort,1)))
        add_wire!(d, Wire(Port(v,OutputPort,1) => wire.target))
        rem_wire!(d, wire)
      end
    end
  end
  return d
end

""" Morphism expression for wires between two boxes.

Assumes that the wires form a permutation morphism.
"""
function hom_expr_between(Ob::Type, diagram::WiringDiagram, v1::Int, v2::Int)
  layer = wiring_layer_between(diagram, v1, v2)
  inputs = to_ob_exprs(Ob, output_ports(diagram, v1))
  outputs = to_ob_exprs(Ob, input_ports(diagram, v2))

  σ = to_permutation(layer)
  @assert !isnothing(σ) "Conversion of non-permutation not implemented"
  @assert inputs == outputs[σ]
  permutation_to_expr(σ, inputs)
end

""" Convert a port value into an object expression.
"""
to_ob_expr(Syntax::Module, x) = to_ob_expr(Syntax.Ob, x)
to_ob_expr(::Type{Ob}, ob::Ob) where Ob = ob
to_ob_expr(Ob::Type, value) = Ob(Ob, value)

to_ob_expr(Ob::Type, ports::Ports) = otimes(to_ob_exprs(Ob, ports))
to_ob_expr(Ob::Type, op::PortOp) =
  invoke_term(parentmodule(Ob), head(op), to_ob_expr(Ob, op.value))

to_ob_exprs(Ob::Type, values) = Ob[ to_ob_expr(Ob, value) for value in values ]

""" Compose morphism expressions, eliminating identities.
"""
function compose_simplify_id(f::GATExpr, g::GATExpr)
  if head(f) == :id; g
  elseif head(g) == :id; f
  else compose(f,g) end
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

""" Convert a junction node to a morphism expression.
"""
function junction_to_expr(Ob::Type, junction::Junction)
  ob = to_ob_expr(Ob, junction.value)
  nin, nout = length(input_ports(junction)), length(output_ports(junction))
  if (nin == 2 && nout == 0) dcounit(ob)
  elseif (nin == 0 && nout == 2) dunit(ob)
  else compose_simplify_id(mmerge_foldl(ob, nin), mcopy_foldl(ob, nout)) end
end

# FIXME: These functions belong elsewhere, probably in the standard library.
function mcopy_foldl(A, n::Int)
  @assert n >= 0
  if (n > 2) compose(mcopy(A), otimes(mcopy_foldl(A, n-1), id(A)))
  elseif (n == 2) mcopy(A)
  elseif (n == 1) id(A)
  else delete(A) end
end
function mmerge_foldl(A, n::Int)
  @assert n >= 0
  if (n > 2) compose(otimes(mmerge_foldl(A, n-1), id(A)), mmerge(A))
  elseif (n == 2) mmerge(A)
  elseif (n == 1) id(A)
  else create(A) end
end

# Graph operations
##################

""" Find parallel compositions in a directed graph.

This two-sided notion of parallel composition is standard in the literature on
series-parallel digraphs.
"""
function find_parallel(g::DiGraph; skip=())
  parallel = Dict{Pair{Int,Int},Vector{Int}}()
  for v in 1:nv(g)
    if v in skip; continue end
    v_in, v_out = inneighbors(g,v), outneighbors(g,v)
    if length(v_in) == 1 && length(v_out) == 1
      u, w = first(v_in), first(v_out)
      push!(get!(parallel, u => w, Int[]), v)
    end
  end
  filter(pair -> length(last(pair)) > 1, parallel)
end

""" Find one-sided parallel compositions in a directed graph.

Finds either input-sided or output-sided compositions. This weaker notion of
parallel composition seems to be nonstandard.
"""
function find_one_sided_parallel(g::DiGraph; input::Bool=true, skip=())
  parallel = Dict{Int,Vector{Int}}()
  for v in 1:nv(g)
    if v in skip; continue end
    vs = input ? inneighbors(g,v) : outneighbors(g,v)
    if length(vs) == 1
      push!(get!(parallel, first(vs), Int[]), v)
    end
  end
  filter(pair -> length(last(pair)) > 1, parallel)
end

""" Find series compositions in a directed graph.
"""
function find_series(g::DiGraph; source=nothing, sink=nothing)::Vector{Vector{Int}}
  series_graph = DiGraph(nv(g))
  for edge in edges(g)
    if (length(outneighbors(g,src(edge))) == 1 &&
        length(inneighbors(g,dst(edge))) == 1 &&
        src(edge) != source && dst(edge) != sink)
      add_edge!(series_graph, edge)
    end
  end
  series = Vector{Int}[]
  for component in weakly_connected_components(series_graph)
    if length(component) > 1
      sub, vmap = induced_subgraph(series_graph, component)
      push!(series, Int[ vmap[v] for v in topological_sort_by_dfs(sub) ])
    end
  end
  series
end

""" Transitive reduction of a directed acyclic graph.

Algorithm described at CS.SE: https://cs.stackexchange.com/a/29133
"""
function transitive_reduction!(g::DiGraph)::DiGraph
  for u in 1:nv(g)
    for v in outneighbors(g, u)
      for w in neighborhood(g, v, nv(g))
        if w != v
          rem_edge!(g, u, w)
        end
      end
    end
  end
  return g
end

end
