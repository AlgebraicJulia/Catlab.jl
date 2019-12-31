""" Algorithms operating on wiring diagrams.
"""
module WiringDiagramAlgorithms
export topological_sort, normalize_cartesian!, normalize_copy!,
  normalize_delete!, crossing_minimization_by_sort

import LightGraphs
using UnionFind
using Statistics: mean

using ..WiringDiagramCore, ..WiringLayers
import ..WiringDiagramCore: set_box

# Traversal
###########

""" Topological sort of boxes in wiring diagram.

Returns a list of box IDs, excluding the outer box's input and output IDs.
"""
function topological_sort(d::WiringDiagram)::Vector{Int}
  vs = LightGraphs.topological_sort_by_dfs(graph(d))
  filter(v -> !(v in outer_ids(d)), vs)
end

# Normalization
###############

""" Put a wiring diagram for a cartesian category into normal form.

This function puts a wiring diagram representing a morphism in a free cartesian
category into normal form. Copies and deletions are simplified as much as
possible.
"""
function normalize_cartesian!(d::WiringDiagram)
  # TODO: By duality, the same algorithm will normalize a cocartesian diagram.
  # We should support cartesian, cocartesian, and bicartesian diagrams.
  normalize_copy!(normalize_delete!(d))
end

""" Normalize copies in a wiring diagram.

This function maximizes sharing of intermediate computations in a wiring
diagram where copies are natural.

This algorithm is basically the same as the congruence closure algorithm on
term graphs, in the special case of the empty relation R = ∅
(Baader & Nipkow, 1998, Term Rewriting and All That, Sec. 4.4).
The main difference is the possibility of zero or many function outputs.
"""
function normalize_copy!(d::WiringDiagram)
  # Compute equivalence classes of boxes (without modifying the diagram).
  uf = UnionFinder(nboxes(d)+2)
  initial = filter(box_ids(d)) do v
    all(u == input_id(d) for u in inneighbors(d,v))
  end
  for v1 in initial
    for v2 in initial
      merge_if_congruent!(d, uf, v1, v2)
    end
  end

  # Keep only the designated representative of each equivalence class.
  extra = Int[]
  for v in box_ids(d)
    rep = find!(uf, v)
    if v != rep
      for wire in out_wires(d, v)
        add_wire!(d, Wire(set_box(wire.source, rep), wire.target))
      end
      push!(extra, v)
    end
  end
  rem_boxes!(d, extra)
  d
end

function merge_if_congruent!(d::WiringDiagram, uf::UnionFinder, v1::Int, v2::Int)
  if v1 == v2 || (find!(uf, v1) != find!(uf, v2) && is_congruent(d, uf, v1, v2))
    union!(uf, v1, v2)
    for out1 in filter(v -> v != output_id(d), outneighbors(d, v1))
      for out2 in filter(v -> v != output_id(d), outneighbors(d, v2))
        merge_if_congruent!(d, uf, out1, out2)
      end
    end
  end
end

function is_congruent(d::WiringDiagram, uf::UnionFinder, v1::Int, v2::Int)::Bool
  box(d, v1) == box(d, v2) && all(eachindex(input_ports(box(d,v1)))) do port
    wires1, wires2 = in_wires(d,v1,port), in_wires(d,v2,port)
    n1, n2 = length(wires1), length(wires2)
    @assert n1 <= 1 && n2 <= 1 # TODO: Handle merges?
    n1 == n2 && all(zip(wires1, wires2)) do pair
      src1, src2 = pair[1].source, pair[2].source
      set_box(src1, find!(uf, src1.box)) == set_box(src2, find!(uf, src2.box))
    end
  end
end

""" Normalize deletions in a wiring diagram.

This function removes all unused intermediate computations in a wiring diagram
where deletion is natural.
"""
function normalize_delete!(d::WiringDiagram)
  unused = Set{Int}()
  for v in reverse(topological_sort(d))
    if all(wire.target.box in unused for wire in out_wires(d, v))
      push!(unused, v)
    end
  end
  rem_boxes!(d, unused)
  d
end

# Layout
########

""" Crossing minimization by sorting a univariate statistic.

The boxes in `sources` and/or `targets` are fixed and the boxes in `vs` are
permuted. A permutation `σ` of the latter is returned, such that `vs[σ]` are the
sorted box IDs. Both one-sided and two-sided crossing minimization are
supported, depending on whether just one, or both, of `sources` and `targets`
are given.

In this simple but popular heuristic algorithm, the boxes are permuted by
sorting a univariate statistic of the positions of incoming and/or outgoing
wires. Typical choices are:

- `mean`: the sample mean, yielding the "barycenter method"
- `median`: the sample median

In both cases, this algorithm has the property that if there is a permutation
with no crossings, it will find it.
"""
function crossing_minimization_by_sort(d::WiringDiagram, vs::Vector{Int};
    sources::Vector{Int}=Int[], targets::Vector{Int}=Int[],
    statistic::Function=mean)::Vector{Int}
  @assert allunique(vs) && allunique(sources) && allunique(targets)
  if isempty(sources) && isempty(targets)
    # Degenerate case: nothing to sort, so preserve original order.
    return collect(eachindex(vs))
  end
  
  source_coord = port_coords(d, sources, OutputPort)
  target_coord = port_coords(d, targets, InputPort)
  stats = map(vs) do v
    source_coords = mapreduce(vcat, sources; init=Int[]) do source
      Int[ source_coord(wire.source) for wire in wires(d, source, v) ]
    end
    target_coords = mapreduce(vcat, targets; init=Int[]) do target
      Int[ target_coord(wire.target) for wire in wires(d, v, target) ]
    end
    statistic(vcat(source_coords, target_coords))
  end
  sortperm(stats)
end

""" Make function mapping ports to logical coordinates.
"""
function port_coords(d::WiringDiagram, vs::Vector{Int}, kind::PortKind)
  get_ports = kind == InputPort ? input_ports : output_ports
  index = Dict(vs[i] => i for i in eachindex(vs))
  sizes = [ length(get_ports(d,v)) for v in vs ]
  offsets = cumsum(vcat([0], sizes))
  (port::Port -> offsets[index[port.box]] + port.port)
end

end
