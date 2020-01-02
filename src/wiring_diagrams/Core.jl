""" Generic data structures for wiring diagrams (aka, string diagrams).

A (directed) wiring diagram consists of a collection of boxes with input and
output ports connected by wires. A box can be atomic (possessing no internal
structure) or can itself be a wiring diagram. Thus, wiring diagrams can be
nested recursively. Wiring diagrams are closely related to what the CS
literature calls "directed graphs with ports" or more simply "port graphs". The
main difference is that a wiring diagram has an "outer box": a wiring diagram
has its own ports that can be connected to the ports of its boxes.

This module provides a generic data structure for wiring diagrams. Arbitrary
data can be attached to the boxes, ports, and wires of a wiring diagram. The
diagrams are "abstract" in the sense that they cannot be directly rendered as
raster or vector graphics. However, they form a useful intermediate
representation that can be serialized to and from GraphML or translated into
Graphviz or other declarative diagram languages.
"""
module WiringDiagramCore
export AbstractBox, Box, WiringDiagram, Wire, Port, PortKind,
  InputPort, OutputPort, input_ports, output_ports, input_id, output_id,
  outer_ids, boxes, box_ids, nboxes, nwires, box, wires, has_wire, graph,
  add_box!, add_boxes!, add_wire!, add_wires!, rem_box!, rem_boxes!, rem_wire!,
  rem_wires!, port_value, validate_ports, is_permuted_equal,
  all_neighbors, neighbors, outneighbors, inneighbors, in_wires, out_wires,
  singleton_diagram, induced_subdiagram, encapsulated_subdiagram,
  substitute, encapsulate

using Compat
using AutoHashEquals
using LightGraphs, MetaGraphs
import LightGraphs: all_neighbors, neighbors, outneighbors, inneighbors

# Data types
############

""" Kind of port: input or output.
"""
@enum PortKind InputPort OutputPort

""" A port on a box to which wires can be connected.
"""
@auto_hash_equals struct Port
  box::Int
  kind::PortKind
  port::Int
end
set_box(port::Port, box::Int) = Port(box, port.kind, port.port)

function Base.isless(p1::Port, p2::Port)::Bool
  # Lexicographic order.
  p1.box < p2.box ||
    (p1.box == p2.box &&
      (p1.kind < p2.kind || (p1.kind == p2.kind && p1.port < p2.port)))
end

""" A wire connecting one port to another.
"""
@auto_hash_equals struct Wire{Value}
  value::Value
  source::Port
  target::Port
end

Wire(value, src::Tuple{Int,PortKind,Int}, tgt::Tuple{Int,PortKind,Int}) =
  Wire(value, Port(src[1],src[2],src[3]), Port(tgt[1],tgt[2],tgt[3]))
Wire(value, src::Tuple{Int,Int}, tgt::Tuple{Int,Int}) =
  Wire(value, Port(src[1],OutputPort,src[2]), Port(tgt[1],InputPort,tgt[2]))
Wire(value, pair::Pair) = Wire(value, first(pair), last(pair))

Wire(src::Port, tgt::Port) = Wire(nothing, src, tgt)
Wire(src::Tuple, tgt::Tuple) = Wire(nothing, src, tgt)
Wire(pair::Pair) = Wire(nothing, first(pair), last(pair))

function Base.show(io::IO, wire::Wire)
  skip_kind = wire.source.kind == OutputPort && wire.target.kind == InputPort
  show_port = (io::IO, port::Port) -> begin
    if skip_kind
      print(io, "($(port.box),$(port.port))")
    else
      print(io, "($(port.box),$(string(port.kind)),$(port.port)")
    end
  end
  print(io, "Wire(")
  if !isnothing(wire.value)
    show(io, wire.value)
    print(io, ", ")
  end
  show_port(io, wire.source)
  print(io, " => ")
  show_port(io, wire.target)
  print(io, ")")
end

function Base.isless(w1::Wire, w2::Wire)::Bool
  # Lexicographic order.
  isless(w1.source, w2.source) ||
    (w1.source == w2.source && isless(w1.target, w2.target))
end

""" Internal wiring diagram data corresponding to `Port`. Do not use directly.
"""
@auto_hash_equals struct PortData
  kind::PortKind
  port::Int
end
to_port_data(port::Port) = PortData(port.kind, port.port)
from_port_data(port::PortData, v::Int) = Port(v, port.kind, port.port)

""" Internal wiring diagram data corresponding to `Wire`. Do not use directly.
"""
@auto_hash_equals struct WireData{Value}
  value::Value
  source::PortData
  target::PortData
end
function to_wire_data(wire::Wire)
  WireData(wire.value, to_port_data(wire.source), to_port_data(wire.target))
end
function from_wire_data(wire::WireData, edge::Edge)
  Wire(wire.value,
       from_port_data(wire.source, src(edge)),
       from_port_data(wire.target, dst(edge)))
end

""" Base type for any box (node) in a wiring diagram.

This type represents an arbitrary black box with inputs and outputs.
"""
abstract type AbstractBox end

input_ports(box::AbstractBox)::Vector = box.input_ports
output_ports(box::AbstractBox)::Vector = box.output_ports

""" An atomic box in a wiring diagram.

These boxes have no internal structure.
"""
@auto_hash_equals struct Box{Value} <: AbstractBox
  value::Value
  input_ports::Vector
  output_ports::Vector
end

Box(inputs::Vector, outputs::Vector) = Box(nothing, inputs, outputs)

function Base.show(io::IO, box::Box)
  print(io, "Box(")
  if !isnothing(box.value)
    show(io, box.value)
    print(io, ", ")
  end
  print(io, "[")
  join(io, [sprint(show, port) for port in box.input_ports], ",")
  print(io, "], [")
  join(io, [sprint(show, port) for port in box.output_ports], ",")
  print(io, "])")
end

""" A directed wiring diagram, aka a string diagram.

The wiring diagram is implemented using the following internal data structures.
A LightGraphs `DiGraph` stores the "skeleton" of the diagram: a simple directed
graph with the boxes as vertices and with an edge between two vertices iff there
is at least one wire between the corresponding boxes. There are two special
vertices, accessible via `input_id` and `output_id`, representing the input and
output ports, respectively.

The `DiGraph` is wrapped inside a `MetaDiGraph` to attach properties to the
vertices and edges. For each edge, an edge property stores the list of wires
between the source and target boxes.
"""
mutable struct WiringDiagram{Theory} <: AbstractBox
  graph::MetaDiGraph
  value::Any
  input_ports::Vector
  output_ports::Vector
  
  function WiringDiagram{T}(value, inputs::Vector, outputs::Vector) where T
    graph = MetaDiGraph()
    diagram = new{T}(graph, value, inputs, outputs)
    add_vertices!(graph, 2)
    return diagram
  end
  function WiringDiagram(d::WiringDiagram{T}) where T
    # Copy constructor for shallow copy.
    new{T}(copy(d.graph), d.value, d.input_ports, d.output_ports)
  end
end

function WiringDiagram{T}(inputs::Vector, outputs::Vector) where T
  WiringDiagram{T}(nothing, inputs, outputs)
end
WiringDiagram(args...) = WiringDiagram{Any}(args...)

input_id(::WiringDiagram) = 1
output_id(::WiringDiagram) = 2
outer_ids(::WiringDiagram) = (1,2)

""" Check equality of wiring diagrams.

Warning: This method checks exact equality of the underlying graph
representation, not mathematical equality which involves graph isomorphism.

See also: `is_permuted_equal`
"""
function Base.:(==)(d1::WiringDiagram, d2::WiringDiagram)
  (input_ports(d1) == input_ports(d2) && output_ports(d1) == output_ports(d2) &&
   d1.value == d2.value && graph(d1) == graph(d2) &&
   boxes(d1) == boxes(d2) && sort!(wires(d1)) == sort!(wires(d2)))
end

""" Check equality of wiring diagram under permutation of boxes.

When the boxes in the first diagram `d1` are permuted according to `σ`,
does it become identical to the second diagram `d2`?
"""
function is_permuted_equal(d1::WiringDiagram, d2::WiringDiagram, σ::Vector{Int})
  @assert nboxes(d1) == length(σ) && nboxes(d2) == length(σ)
  d1_ids, d2_ids = box_ids(d1), box_ids(d2)
  box_map = Dict{Int,Int}(d1_ids[σ[i]] => d2_ids[i] for i in eachindex(σ))
  is_induced_equal(d1, d2, box_map)
end
function is_induced_equal(d1::WiringDiagram, d2::WiringDiagram, box_map::Dict{Int,Int})
  box_map[input_id(d1)] = input_id(d2)
  box_map[output_id(d1)] = output_id(d2)
  map_wire = wire::Wire -> Wire(wire.value,
    set_box(wire.source, box_map[wire.source.box]),
    set_box(wire.target, box_map[wire.target.box]))
  (input_ports(d1) == input_ports(d2) && output_ports(d1) == output_ports(d2) &&
   all(box(d1,v) == box(d2,box_map[v]) for v in box_ids(d1)) &&
   sort!(map(map_wire, wires(d1))) == sort!(wires(d2)))
end

Base.copy(diagram::WiringDiagram) = WiringDiagram(diagram)

function Base.show(io::IO, diagram::WiringDiagram{T}) where T
  sshowcompact = x -> sprint(show, x, context=:compact => true)
  print(io, "WiringDiagram")
  if T != Any
    print(io, "{$T}")
  end
  print(io, "(")
  if !isnothing(diagram.value)
    show(io, diagram.value)
    print(io, ", ")
  end
  print(io, "[")
  join(io, map(sshowcompact, input_ports(diagram)), ",")
  print(io, "], [")
  join(io, map(sshowcompact, output_ports(diagram)), ",")
  print(io, "], ")
  if get(io, :compact, false)
    print(io, "{$(nboxes(diagram)) boxes}, {$(nwires(diagram)) wires}")
  else
    print(io, "\n[ $(input_id(diagram)) => {inputs},\n  ")
    print(io, "$(output_id(diagram)) => {outputs},\n  ")
    join(io, [ "$v => $(sshowcompact(box(diagram, v)))"
               for v in box_ids(diagram) ], ",\n  ")
    print(io, " ],\n[ ")
    join(io, map(sshowcompact, wires(diagram)), ",\n  ")
    print(io, " ]")
  end
  print(io, ")")
end

# Imperative interface
######################

# Basic accessors.

box(f::WiringDiagram, v::Int) = get_prop(f.graph, v, :box)
boxes(f::WiringDiagram) = AbstractBox[ box(f,v) for v in box_ids(f) ]
nboxes(f::WiringDiagram) = nv(graph(f)) - 2

function box_ids(f::WiringDiagram)
  Int[ v for v in 1:nv(graph(f)) if !(v in outer_ids(f)) ]
end

function wires(f::WiringDiagram, edge::Edge)
  if has_edge(f.graph, edge)
    Wire[ from_wire_data(data, edge) for data in get_prop(f.graph,edge,:wires) ]
  else
    Wire[]
  end
end
wires(f::WiringDiagram, src::Int, tgt::Int) = wires(f, Edge(src,tgt))
wires(f::WiringDiagram) = vcat((wires(f,e) for e in edges(graph(f)))...)
nwires(f::WiringDiagram) =
  sum(Int[ length(get_prop(f.graph,e,:wires)) for e in edges(graph(f)) ])

function has_wire(f::WiringDiagram, src::Int, tgt::Int)
  has_edge(graph(f), Edge(src, tgt))
end
function has_wire(f::WiringDiagram, wire::Wire)
  wire in wires(f, wire.source.box, wire.target.box)
end
has_wire(f::WiringDiagram, pair::Pair) = has_wire(f, Wire(pair))

function input_ports(f::WiringDiagram, v::Int)
  if v == input_id(f)
    error("Input vertex does not have input ports within wiring diagram")
  elseif v == output_id(f)
    output_ports(f)
  else
    input_ports(box(f, v))
  end
end

function output_ports(f::WiringDiagram, v::Int)
  if v == input_id(f)
    input_ports(f)
  elseif v == output_id(f)
    error("Output vertex does not have output ports within wiring diagram")
  else
    output_ports(box(f, v))
  end
end

function port_value(f::WiringDiagram, port::Port)
  get_ports = port.kind == InputPort ? input_ports : output_ports
  get_ports(f, port.box)[port.port]
end

# Graph mutation.

function add_box!(f::WiringDiagram, box::AbstractBox)
  @assert add_vertex!(f.graph, :box, box)
  return nv(f.graph)
end

function add_boxes!(f::WiringDiagram, boxes)
  for box in boxes
    add_box!(f, box)
  end
end

function rem_box!(f::WiringDiagram, v::Int)
  @assert !(v in outer_ids(f))
  rem_vertex!(f.graph, v)
end

function rem_boxes!(f::WiringDiagram, vs)
  # Remove boxes in descending order of vertex ID to maintain ID stability.
  for v in sort!(collect(vs), rev=true)
    rem_box!(f, v)
  end
end

function add_wire!(f::WiringDiagram, wire::Wire)
  # Check compatibility of port types.
  validate_ports(port_value(f, wire.source), port_value(f, wire.target))
  
  # Add edge and edge properties.
  edge = Edge(wire.source.box, wire.target.box)
  if !has_edge(f.graph, edge)
    add_edge!(f.graph, src(edge), dst(edge), :wires, WireData[])
  end
  push!(get_prop(f.graph, edge, :wires), to_wire_data(wire))
end
add_wire!(f::WiringDiagram, pair::Pair) = add_wire!(f, Wire(pair))

function add_wires!(f::WiringDiagram, wires)
  for wire in wires
    add_wire!(f, wire)
  end
end

function rem_wire!(f::WiringDiagram, wire::Wire)
  edge = Edge(wire.source.box, wire.target.box)
  edge_data = to_wire_data(wire)
  wires = get_prop(f.graph, edge, :wires)
  deleteat!(wires, findlast(d -> d == edge_data, wires))
  if isempty(wires)
    rem_edge!(f.graph, edge)
  end
end
rem_wire!(f::WiringDiagram, pair::Pair) = rem_wire!(f, Wire(pair))

function rem_wires!(f::WiringDiagram, wires)
  for wire in wires
    rem_wire!(f, wire)
  end
end

function rem_wires!(f::WiringDiagram, src::Int, tgt::Int)
  rem_edge!(f.graph, Edge(src, tgt))
end

""" Check compatibility of source and target ports.

The default implementation is a no-op.
"""
function validate_ports(source_port, target_port) end

# Graph properties.

""" Retrieve the underlying LightGraphs graph.

Do not mutate it! All mutations should pass through the `WiringDiagram` methods:
`add_box!`, `rem_box!`, etc.
"""
graph(diagram::WiringDiagram) = diagram.graph.graph

# Convenience methods delegated to LightGraphs.
all_neighbors(d::WiringDiagram, v::Int) = all_neighbors(graph(d), v)
neighbors(d::WiringDiagram, v::Int) = neighbors(graph(d), v)
outneighbors(d::WiringDiagram, v::Int) = outneighbors(graph(d), v)
inneighbors(d::WiringDiagram, v::Int) = inneighbors(graph(d), v)

""" Get all wires coming into or out of the box.
"""
function wires(d::WiringDiagram, v::Int)
  result = wires(d, v, v)
  for u in inneighbors(d, v)
    if u != v
      append!(result, wires(d, u, v))
    end
  end
  for u in outneighbors(d, v)
    if u != v
      append!(result, wires(d, v, u))
    end
  end
  result
end

""" Get all wires coming into the box.
"""
function in_wires(d::WiringDiagram, v::Int)
  result = Wire[]
  for u in inneighbors(d, v)
    append!(result, wires(d, u, v))
  end
  result
end

""" Get all wires coming into the port.
"""
function in_wires(d::WiringDiagram, port::Port)
  result = Wire[]
  for v in inneighbors(d, port.box)
    for wire in wires(d, v, port.box)
      if wire.target == port
        push!(result, wire)
      end
    end
  end
  result
end
function in_wires(d::WiringDiagram, v::Int, port::Int)
  in_wires(d, Port(v, InputPort, port))
end

""" Get all wires coming out of the box.
"""
function out_wires(d::WiringDiagram, v::Int)
  result = Wire[]
  for u in outneighbors(d, v)
    append!(result, wires(d, v, u))
  end
  result
end

""" Get all wires coming out of the port.
"""
function out_wires(d::WiringDiagram, port::Port)
  result = Wire[]
  for v in outneighbors(d, port.box)
    for wire in wires(d, port.box, v)
      if wire.source == port
        push!(result, wire)
      end
    end
  end
  result
end
function out_wires(d::WiringDiagram, v::Int, port::Int)
  out_wires(d, Port(v, OutputPort, port))
end

# Other constructors.

""" A wiring diagram with a single box connected to its outer ports.
"""
function singleton_diagram(T::Type, box::AbstractBox)
  inputs, outputs = input_ports(box), output_ports(box)
  d = WiringDiagram{T}(inputs, outputs)
  v = add_box!(d, box)
  add_wires!(d, ((input_id(d),i) => (v,i) for i in eachindex(inputs)))
  add_wires!(d, ((v,i) => (output_id(d),i) for i in eachindex(outputs)))
  return d
end
singleton_diagram(box::AbstractBox) = singleton_diagram(Any, box)

""" The wiring diagram induced by a subset of its boxes.

See also `encapsulated_subdiagram`.
"""
function induced_subdiagram(d::WiringDiagram{T}, vs::Vector{Int}) where T
  sub = WiringDiagram{T}(input_ports(d), output_ports(d))
  vmap = Dict(input_id(d) => input_id(sub), output_id(d) => output_id(sub))
  for v in vs
    vmap[v] = add_box!(sub, box(d, v))
  end
  for wire in wires(d)
    src, tgt = wire.source, wire.target
    if haskey(vmap, src.box) && haskey(vmap, tgt.box)
      add_wire!(sub,
        Wire(set_box(src, vmap[src.box]), set_box(tgt, vmap[tgt.box])))
    end
  end
  return sub
end

# Substitution
##############

""" Substitute wiring diagrams for boxes.

Performs one or more substitutions. When performing multiple substitutions, the
substitutions are simultaneous.

This operation implements the operadic composition of wiring diagrams
(`ocompose`).
"""
function substitute(d::WiringDiagram; kw...)
  substitute(d, filter(v -> box(d,v) isa WiringDiagram, box_ids(d)); kw...)
end
function substitute(d::WiringDiagram, v::Int; kw...)
  substitute(d, v, box(d,v)::WiringDiagram; kw...)
end
function substitute(d::WiringDiagram, vs::Vector{Int}; kw...)
  substitute(d, vs, WiringDiagram[ box(d,v) for v in vs ]; kw...)
end
function substitute(d::WiringDiagram, v::Int, sub::WiringDiagram; kw...)
  substitute(d, [v], [sub]; kw...)
end

function substitute(d::WiringDiagram{T}, vs::Vector{Int}, subs::Vector{<:WiringDiagram};
                    merge_wire_values=default_merge_wire_values) where T
  # In outline, the algorithm is:
  #
  # 1. Create an empty wiring diagram.
  # 2. Add *all* boxes of original diagram and the diagrams to be substituted
  #    (in the appropriate order).
  # 3. Add *all* wires of original diagram and the diagrams to be substituted.
  # 4. Remove the boxes that were substituted (hence also removing extraneous
  #    wires from step 3).
  #
  # This may seem convoluted, but it is the simplest way I know to handle the
  # problem of *instantaneous wires*. Some authors ban instantaneous wires, but
  # we need them to represent identities, braidings, etc.
  @assert length(vs) == length(subs)
  result = WiringDiagram{T}(d.value, input_ports(d), output_ports(d))
  
  # Add boxes by interleaving, in the correct order, the non-substituted boxes
  # of the original diagram and the internal boxes of the substituted diagrams.
  # At the very end, add the substituted boxes too.
  vmap = Dict(input_id(d) => input_id(result), output_id(d) => output_id(result))
  sub_maps = Dict(zip(vs, ((sub, Dict{Int,Int}()) for sub in subs)))
  for v in box_ids(d)
    if haskey(sub_maps, v)
      sub, sub_map = sub_maps[v]
      for u in box_ids(sub)
        sub_map[u] = add_box!(result, box(sub, u))
      end
    else
      vmap[v] = add_box!(result, box(d, v))
    end
  end
  for v in vs
    vmap[v] = add_box!(result, box(d, v))
  end
  
  # Add the wires of the original diagram, then add the internal wires of the
  # substituted diagrams.
  for wire in wires(d)
    add_wire!(result, Wire(wire.value,
      set_box(wire.source, vmap[wire.source.box]),
      set_box(wire.target, vmap[wire.target.box])))
  end
  for v in vs
    substitute_wires!(result, vmap[v], sub_maps[v]...;
      merge_wire_values=merge_wire_values)
  end
  
  # Finally, remove the substituted boxes. Because they were added last, this
  # will not change the IDs of the other boxes.
  rem_boxes!(result, (vmap[v] for v in vs))
  result
end

""" Substitute wires of sub-diagram into containing wiring diagram.
"""
function substitute_wires!(d::WiringDiagram, v::Int,
                           sub::WiringDiagram, sub_map::Dict{Int,Int};
                           merge_wire_values=default_merge_wire_values)
  for wire in wires(sub)
    src = get(sub_map, wire.source.box, 0)
    tgt = get(sub_map, wire.target.box, 0)
    # Special case: wire from input port to output port.
    if wire.source.box == input_id(sub) && wire.target.box == output_id(sub)
      for in_wire in in_wires(d, v, wire.source.port)
        for out_wire in out_wires(d, v, wire.target.port)
          add_wire!(d, Wire(
            merge_wire_values(in_wire.value, wire.value, out_wire.value),
            in_wire.source, out_wire.target))
        end
      end
    # Special case: wire from input port to internal box.
    elseif wire.source.box == input_id(sub)
      for in_wire in in_wires(d, v, wire.source.port)
        add_wire!(d, Wire(
          merge_wire_values(in_wire.value, wire.value, nothing),
          in_wire.source, set_box(wire.target, tgt)))
      end
    # Special case: wire from internal box to output port.
    elseif wire.target.box == output_id(sub)
      for out_wire in out_wires(d, v, wire.target.port)
        add_wire!(d, Wire(
          merge_wire_values(nothing, wire.value, out_wire.value),
          set_box(wire.source, src), out_wire.target))
      end
    # Default case: wire between two internal boxes.
    else
      add_wire!(d, Wire(
        merge_wire_values(nothing, wire.value, nothing),
        set_box(wire.source, src), set_box(wire.target, tgt)))
    end
  end
end

default_merge_wire_values(::Any, middle::Any, ::Any) = middle

# Encapsulation
###############

""" Encapsulate multiple boxes within a single sub-diagram.

This operation is a (one-sided) inverse to subsitution (see `substitute`).
"""
function encapsulate(d::WiringDiagram, vs::Vector{Int}; value=nothing, kw...)
  encapsulate(d, [vs]; values=[value], kw...)
end

function encapsulate(d::WiringDiagram{T}, vss::Vector{Vector{Int}};
    discard_boxes::Bool=false, make_box=Box, values=nothing) where T
  if isempty(vss); return d end
  if any(isempty(vs) for vs in vss)
    error("Cannot encapsulate an empty set of boxes")
  end
  if !allunique(reduce(vcat, vss))
    error("Cannot encapsulate overlapping sets of boxes")
  end
  if isnothing(values)
    values = repeat([nothing], length(vss))
  end
  result = WiringDiagram{T}(d.value, input_ports(d), output_ports(d))
  
  # Add boxes, both encapsulated and non-encapsulated, to new wiring diagram.
  encapsulated_representatives = Dict(
    minimum(vs) => (vs, value) for (vs, value) in zip(vss, values))
  all_encapsulated = Set(v for vs in vss for v in vs)
  vmap = Dict(input_id(d) => input_id(result), output_id(d) => output_id(result))
  port_map = Dict{Port,Port}()
  for v in box_ids(d)
    if haskey(encapsulated_representatives, v)
      vs, value = encapsulated_representatives[v]
      sub, sub_map = encapsulated_subdiagram(d, vs;
        discard_boxes=discard_boxes, make_box=make_box, value=value)
      subv = add_box!(result, sub)
      merge!(port_map, Dict(
        port => from_port_data(data, subv) for (port, data) in sub_map))
    elseif v ∉ all_encapsulated
      vmap[v] = add_box!(result, box(d, v))
    end
  end
  
  # Add wires to new wiring diagram.
  for wire in wires(d)
    src, tgt = wire.source, wire.target
    new_src = if haskey(vmap, src.box); set_box(src, vmap[src.box])
      elseif haskey(port_map, src); port_map[src]
      else; continue end
    new_tgt = if haskey(vmap, tgt.box); set_box(tgt, vmap[tgt.box])
      elseif haskey(port_map, tgt); port_map[tgt]
      else; continue end
    add_wire!(result, Wire(new_src, new_tgt))
  end
  result
end

""" Create an encapsulating box for a set of boxes in a wiring diagram.

To a first approximation, the union of input ports of the given boxes will
become the inputs ports of the encapsulating box and likewise for the output
ports. However, when copies or merges occur, as in a cartesian or cocartesian
category, a simplification procedure may reduce the number of ports on the
encapsulating box.

Specifically:

1. Each input port of an encapsulated box will have at most one incoming wire
from the encapsulating outer box, and each output port of an encapsulated box
will have at most one outgoing wire to the encapsulating outer box.

2. A set of ports connected to the same outside (non-encapsulated) ports will be
simplified into a single port of the encapsulating box.

See also `induced_subdiagram`.
"""
function encapsulated_subdiagram(d::WiringDiagram{T}, vs::Vector{Int};
    discard_boxes::Bool=false, make_box=Box, value=nothing) where T
  # Add encapsulated box to new wiring diagram.
  inputs, outputs = [], []
  result = discard_boxes ? nothing : WiringDiagram{T}(value, inputs, outputs)
  vmap = if discard_boxes
    Dict(v => nothing for v in vs)
  else
    Dict(v => add_box!(result, box(d, v)) for v in vs)
  end
  
  # Process wires into, or out of, encapsulated boxes.
  port_map = Dict{Port,PortData}()
  inner_port_map = Dict{Tuple{Vector{Port},Any},Int}()
  for v in vs
    # Add input ports to encapsulating box and corresponding wire.
    for (port, value) in enumerate(input_ports(d, v))
      tgt = Port(v, InputPort, port)
      srcs = sort!([ wire.source for wire in in_wires(d, tgt)
                     if !haskey(vmap, wire.source.box) ])
      if isempty(srcs) continue end
      src = get!(inner_port_map, (srcs, value)) do
        push!(inputs, value)
        port_data = port_map[tgt] = PortData(InputPort, length(inputs))
        port_data.port
      end
      if discard_boxes; continue end
      add_wire!(result,
        Wire(Port(input_id(result), OutputPort, src), set_box(tgt, vmap[v])))
    end
    
    # Add output ports to encapsulating box and corresponding wire.
    for (port, value) in enumerate(output_ports(d, v))
      src = Port(v, OutputPort, port)
      tgts = sort([ wire.target for wire in out_wires(d, src)
                    if !haskey(vmap, wire.target.box) ])
      if isempty(tgts) continue end
      tgt = get!(inner_port_map, (tgts, value)) do
        push!(outputs, value)
        port_data = port_map[src] = PortData(OutputPort, length(outputs))
        port_data.port
      end
      if discard_boxes; continue end
      add_wire!(result,
        Wire(set_box(src, vmap[v]), Port(output_id(result), InputPort, tgt)))
    end
    
    # Add wires between two encapsulated boxes.
    if discard_boxes; continue end
    for wire in out_wires(d, v)
      src, tgt = wire.source, wire.target
      if haskey(vmap, src.box) && haskey(vmap, tgt.box) # Clause #1 always true.
        add_wire!(result,
          Wire(set_box(src, vmap[src.box]), set_box(tgt, vmap[tgt.box])))
      end
    end
  end
  
  # Yield input and output port lists with the tightest possible types.
  inputs, outputs = [ x for x in inputs ], [ x for x in outputs ]
  if discard_boxes
    result = make_box(value, inputs, outputs)
  else
    result.input_ports, result.output_ports = inputs, outputs
  end
  (result, port_map)
end

end
