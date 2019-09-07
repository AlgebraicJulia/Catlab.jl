""" Algorithms operating on wiring diagrams.
"""
module WiringDiagramAlgorithms
export Junction, add_junctions!, rem_junctions!,
  normalize_cartesian!, normalize_copy!, normalize_delete!,
  topological_sort, crossing_minimization_by_sort

using AutoHashEquals
import LightGraphs
using UnionFind
using Statistics: mean

using ..WiringDiagramCore, ..WiringLayers
import ..WiringDiagramCore: input_ports, output_ports, set_box

# Traversal
###########

""" Topological sort of boxes in wiring diagram.

Returns a list of box IDs, excluding the outer box's input and output IDs.
"""
function topological_sort(d::WiringDiagram)::Vector{Int}
  vs = LightGraphs.topological_sort_by_dfs(graph(d))
  outer_ids = (input_id(d), output_id(d))
  filter(v -> v ∉ outer_ids, vs)
end

# Diagonals and codiagonals
###########################

""" Junction node in a wiring diagram.

Used to explicitly represent copies, merges, deletions, and creations.
"""
@auto_hash_equals struct Junction{Value} <: AbstractBox
  value::Value
  ninputs::Int
  noutputs::Int
end
input_ports(junction::Junction) = repeat([junction.value], junction.ninputs)
output_ports(junction::Junction) = repeat([junction.value], junction.noutputs)

""" Add junction nodes to wiring diagram.

Transforms from implicit to explicit representation of (co)diagonals.
"""
function add_junctions!(d::WiringDiagram)
  add_output_junctions!(d, input_id(d))
  add_input_junctions!(d, output_id(d))
  for v in box_ids(d)
    add_input_junctions!(d, v)
    add_output_junctions!(d, v)
  end
  return d
end
function add_input_junctions!(d::WiringDiagram, v::Int)
  for (port, port_value) in enumerate(input_ports(d, v))
    wires = in_wires(d, v, port)
    nwires = length(wires)
    if nwires != 1
      rem_wires!(d, wires)
      jv = add_box!(d, Junction(port_value, nwires, 1))
      add_wire!(d, Port(jv, OutputPort, 1) => Port(v, InputPort, port))
      add_wires!(d, [ wire.source => Port(jv, InputPort, i)
                      for (i, wire) in enumerate(wires) ])
    end
  end
end
function add_output_junctions!(d::WiringDiagram, v::Int)
  for (port, port_value) in enumerate(output_ports(d, v))
    wires = out_wires(d, v, port)
    nwires = length(wires)
    if nwires != 1
      rem_wires!(d, wires)
      jv = add_box!(d, Junction(port_value, 1, nwires))
      add_wire!(d, Port(v, OutputPort, port) => Port(jv, InputPort, 1))
      add_wires!(d, [ Port(jv, OutputPort, i) => wire.target
                      for (i, wire) in enumerate(wires) ])
    end
  end
end

""" Remove junction nodes from wiring diagram.

Transforms from explicit to implicit representation of (co)diagonals.
"""
function rem_junctions!(d::WiringDiagram)
  junction_ids = filter(v -> box(d,v) isa Junction, box_ids(d))
  junction_diagrams = map(junction_ids) do v
    junction = box(d,v)::Junction
    layer = complete_layer(junction.ninputs, junction.noutputs)
    to_wiring_diagram(layer, input_ports(junction), output_ports(junction))
  end
  substitute!(d, junction_ids, junction_diagrams)
  return d
end

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
