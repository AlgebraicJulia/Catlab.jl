""" Algorithms operating on wiring diagrams.
"""
module WiringDiagramAlgorithms
export topological_sort, crossing_minimization_by_sort,
  normalize_cartesian!, normalize_copy!, normalize_delete!

import LightGraphs
using UnionFind
using Statistics: mean

using ..WiringDiagramCore
import ..WiringDiagramCore: set_box

# Traversal
###########

""" Topological sort of boxes in wiring diagram.

Returns a list of box IDs, excluding the special input and output IDs.
"""
function topological_sort(d::WiringDiagram)::Vector{Int}
  vs = LightGraphs.topological_sort_by_dfs(graph(d))
  skip = (input_id(d), output_id(d))
  filter(v -> !(v in skip), vs)
end

# Normal forms
##############

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

""" One-sided crossing minimization by sorting a univariate statistic.

The boxes in `sources` are fixed and the boxes in `targets` are permuted.
A permutation `σ` of the latter is returned, such that `targets[σ]` are the
sorted box IDs.

In this popular heuristic algorithm, the boxes are permuted by sorting a
univariate statistic of the positions of incoming wires. Typical choices are:

- `mean`: the sample mean, yielding the "barycenter method"
- `median`: the sample median

In both cases, this algorithm has the property that if there is a permutation
with no crossings, it will find it.
"""
function crossing_minimization_by_sort(
    d::WiringDiagram, sources::Vector{Int}, targets::Vector{Int};
    statistic::Function=mean)::Vector{Int}
  @assert allunique(sources) && allunique(targets)
  
  index = Dict(sources[i] => i for i in eachindex(sources))
  sizes = [ length(output_ports(d,v)) for v in sources ]
  offsets = cumsum(vcat([0], sizes))
  source_coord(port::Port) = offsets[index[port.box]] + port.port
  
  stats = map(targets) do target
    coords = mapreduce(vcat, sources; init=[]) do source
      [ source_coord(wire.source) for wire in wires(d, source, target) ]
    end
    statistic(coords)
  end
  sortperm(stats)
end

end
