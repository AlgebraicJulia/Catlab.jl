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

using Compat
using LightGraphs

using ...Syntax
using ...Doctrines: id, compose, otimes, munit, mcopy, mmerge, create, delete
using ...Doctrines.Permutations
using ..WiringDiagramCore, ..WiringLayers
import ..WiringLayers: to_wiring_diagram
using ..WiringDiagramAlgorithms: Junction, add_junctions!,
  crossing_minimization_by_sort

# Expression -> Diagram
#######################

""" Convert a morphism expression into a wiring diagram.

The morphism expression should belong to the doctrine of symmetric monoidal
categories, possibly with diagonals and codiagonals. Thus, the doctrines of
cartesian, cocartesian, and biproduct categories are supported.
"""
function to_wiring_diagram(expr::GATExpr)
  functor((Ports, WiringDiagram), expr;
    terms = Dict(
      :Ob => expr -> Ports([first(expr)]),
      :Hom => expr -> singleton_diagram(Box(expr)),
    )
  )
end

# Diagram -> Expression
#######################

""" Convert a wiring diagram into a morphism expression.
"""
function to_hom_expr(Ob::Type, Hom::Type, d::WiringDiagram)
  box_to_expr(v::Int) = to_hom_expr(Ob, Hom, box(d,v))
  
  # Step 0: Reduction: Add junction nodes to ensure any wiring layer between
  # two boxes is a permutation.
  d = copy(d)
  add_junctions!(d)
  
  # Special case: no boxes.
  if nboxes(d) == 0
    return hom_expr_between(Ob, d, input_id(d), output_id(d))
  end
  
  # Step 1. Transitive reduction.
  transitive_reduction!(Ob, d)

  # Step 2. Alternating series- and parallel-reduction.
  n = nboxes(d)
  while true
    parallel_reduction!(Ob, Hom, d)
    series_reduction!(Ob, Hom, d)
    # Repeat until the box count stops decreasing.
    nboxes(d) >= n && break
    n = nboxes(d)
  end
  
  # Termination: process all remaining boxes (always at least one, and exactly
  # one if there is no creation or deletion).
  if nboxes(d) > 1
    product = otimes(map(box_to_expr, box_ids(d)))
    encapsulate!(d, box_ids(d), discard_boxes=true, value=product)
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

function to_hom_expr(Ob::Type, Hom::Type, box::Box)
  if box.value isa Hom
    box.value
  else
    dom = otimes(ports_to_obs(Ob, input_ports(box)))
    codom = otimes(ports_to_obs(Ob, output_ports(box)))
    Hom(box.value, dom, codom)
  end
end
function to_hom_expr(Ob::Type, Hom::Type, junction::Junction)
  junction_to_expr(Ob, junction)
end

""" All possible parallel reductions of a wiring diagram.
"""
function parallel_reduction!(Ob::Type, Hom::Type, d::WiringDiagram)
  parallel = Vector{Int}[]
  parallel_unsorted = find_parallel(graph(d), source=input_id(d), sink=output_id(d))
  products = map(collect(parallel_unsorted)) do ((source, target), vs)
    exprs = Hom[ to_hom_expr(Ob, Hom, box(d,v)) for v in vs ]
    σ = crossing_minimization_by_sort(d, vs,
      sources = isnothing(source) ? Int[] : [source],
      targets = isnothing(target) ? Int[] : [target])
    push!(parallel, vs[σ])
    otimes(exprs[σ])
  end
  
  if !isempty(parallel)
    encapsulate!(d, parallel, discard_boxes=true, values=products)
  end
  return d
end

""" All possible series reductions of a wiring diagram.
"""
function series_reduction!(Ob::Type, Hom::Type, d::WiringDiagram)
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
  
  if !isempty(series)
    encapsulate!(d, series, discard_boxes=true, values=composites)
  end
  return d
end

""" All possible transitive reductions of a wiring diagram.
"""
function transitive_reduction!(Ob::Type, d::WiringDiagram)
  reduced = transitive_reduction!(copy(graph(d)))
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
  inputs = ports_to_obs(Ob, output_ports(diagram, v1))
  outputs = ports_to_obs(Ob, input_ports(diagram, v2))
  
  σ = to_permutation(layer)
  @assert !isnothing(σ) "Conversion of non-permutation not implemented"
  @assert inputs == outputs[σ]
  permutation_to_expr(σ, inputs)
end

coerce_ob(Ob::Type, x) = x isa Ob ? x : Ob(Ob,x)
ports_to_obs(Ob::Type, ports) = Ob[ coerce_ob(Ob, port) for port in ports ]

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
  ob = coerce_ob(Ob, junction.value)
  compose_simplify_id(
    mmerge_foldl(ob, junction.ninputs),
    mcopy_foldl(ob, junction.noutputs)
  )
end

# FIXME: These functions belong elsewhere, probably in the standard library.
function mcopy_foldl(A, n::Int)
  @assert n >= 0
  if n > 2
    compose(mcopy(A), otimes(mcopy_foldl(A, n-1), id(A)))
  elseif n == 2
    mcopy(A)
  elseif n == 1
    id(A)
  else # n == 0
    delete(A)
  end
end
function mmerge_foldl(A, n::Int)
  @assert n >= 0
  if n > 2
    compose(otimes(mmerge_foldl(A, n-1), id(A)), mmerge(A))
  elseif n == 2
    mmerge(A)
  elseif n == 1
    id(A)
  else # n == 0
    create(A)
  end
end

# Graph operations
##################

""" Find parallel compositions in a directed graph.
"""
function find_parallel(g::DiGraph; source=nothing, sink=nothing)
  parallel = Dict{Pair{Union{Int,Nothing},Union{Int,Nothing}},Vector{Int}}()
  for v in 1:nv(g)
    if v in (source, sink); continue end
    # Note: The definition in the literature on series-parallel digraphs
    # requires that `length(v_in) == 1 && length(v_out) == 1`.
    # Replacing the conjunction with a disjunction allows more general
    # parallel reductions while still ensuring that no vertex is counted as
    # parallel in more than one place.
    v_in, v_out = inneighbors(g,v), outneighbors(g,v)
    if length(v_in) == 1 || length(v_out) == 1
      for u in (isempty(v_in) ? [nothing] : v_in)
        for w in (isempty(v_out) ? [nothing] : v_out)
          push!(get!(parallel, u => w, Int[]), v)
        end
      end
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
