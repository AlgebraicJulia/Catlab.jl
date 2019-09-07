""" Generic data structure for wiring diagrams (aka, string diagrams).

A (directed) wiring diagram consists of a collection of boxes with input and
output ports connected by wires. A box can be atomic (possessing no internal
structure) or can itself be a wiring diagram. Thus, wiring diagrams can be
nested recursively. Wiring diagrams are closely related to what the CS
literature calls "directed graphs with ports" or more simply "port graphs". The
main difference is that a wiring diagram has an "outer box": a wiring diagram
has its own ports that can be connected to the ports of its boxes.

This module offers a generic data structure for wiring diagrams. Arbitrary data
can be attached to the boxes, ports, and wires of a wiring diagram. There is a
low-level interface for direct manipulation of boxes and wires and a high-level
interface based on the theory of symmetric monoidal categories. 

The wiring diagrams in this module are "abstract" in the sense that they cannot
be directly rendered as raster or vector graphics. However, they form a useful
intermediate representation that can be straightforwardly serialized to and from
GraphML or translated into Graphviz or other declarative diagram languages.
"""
module WiringDiagramCore

export AbstractBox, Box, WiringDiagram, Wire, Ports, PortValueError, Port,
  PortKind, InputPort, OutputPort, input_ports, output_ports, port_value,
  input_id, output_id, to_wiring_diagram, boxes, box_ids, nboxes, nwires, box,
  wires, has_wire, graph, add_box!, add_boxes!, add_wire!, add_wires!,
  rem_box!, rem_boxes!, rem_wire!, rem_wires!, validate_ports,
  all_neighbors, neighbors, outneighbors, inneighbors, in_wires, out_wires,
  substitute!, encapsulate!,
  dom, codom, id, compose, otimes, munit, braid, mcopy, delete, mmerge, create,
  permute, is_permuted_equal

using Compat
using AutoHashEquals
using LightGraphs, MetaGraphs
import LightGraphs: all_neighbors, neighbors, outneighbors, inneighbors

using ...GAT, ...Syntax
import ...Doctrines:
  CategoryExpr, ObExpr, HomExpr, MonoidalCategoryWithBidiagonals,
  dom, codom, id, compose, otimes, munit, braid, mcopy, delete, mmerge, create

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

""" Internal data structure corresponding to `Port`. Do not use directly.
"""
@auto_hash_equals struct PortEdgeData
  kind::PortKind
  port::Int
end
to_edge_data(port::Port) = PortEdgeData(port.kind, port.port)
from_edge_data(port::PortEdgeData, v::Int) = Port(v, port.kind, port.port)

""" Internal data structure corresponding to `Wire`. Do not use directly.
"""
@auto_hash_equals struct WireEdgeData{Value}
  value::Value
  source::PortEdgeData
  target::PortEdgeData
end
function to_edge_data(wire::Wire)
  WireEdgeData(wire.value, to_edge_data(wire.source), to_edge_data(wire.target))
end
function from_edge_data(wire::WireEdgeData, edge::Edge)
  Wire(wire.value,
       from_edge_data(wire.source, src(edge)),
       from_edge_data(wire.target, dst(edge)))
end

""" List of ports: object in the category of wiring diagrams.
"""
@auto_hash_equals struct Ports{Value}
  ports::Vector{Value}
end
Base.eachindex(A::Ports) = eachindex(A.ports)
Base.length(A::Ports) = length(A.ports)

""" Error thrown when the source and target ports of a wire are incompatible.
"""
struct PortValueError <: Exception
  source_port::Any
  target_port::Any
end
function Base.showerror(io::IO, exc::PortValueError)
  print(io, `Ports $(exc.source_port) and $(exc.target_port) are incompatible`)
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

""" Wiring diagram: morphism in the category of wiring diagrams.

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
mutable struct WiringDiagram <: AbstractBox
  graph::MetaDiGraph
  value::Any
  input_ports::Vector
  output_ports::Vector
  input_id::Int
  output_id::Int
  
  function WiringDiagram(value::Any, input_ports::Vector, output_ports::Vector)
    graph = MetaDiGraph()
    diagram = new(graph, value, input_ports, output_ports, 1, 2)
    add_vertices!(graph, 2)
    return diagram
  end
  function WiringDiagram(d::WiringDiagram)
    # Copy constructor for shallow copy.
    graph = copy(d.graph)
    new(graph, d.value, d.input_ports, d.output_ports, d.input_id, d.output_id)
  end
end

function WiringDiagram(input_ports::Vector, output_ports::Vector)
  WiringDiagram(nothing, input_ports, output_ports)
end
function WiringDiagram(value::Any, inputs::Ports, outputs::Ports)
  WiringDiagram(value, inputs.ports, outputs.ports)
end
function WiringDiagram(inputs::Ports, outputs::Ports)
  WiringDiagram(inputs.ports, outputs.ports)
end

input_id(diagram::WiringDiagram) = diagram.input_id
output_id(diagram::WiringDiagram) = diagram.output_id

""" Check equality of wiring diagrams.

Warning: This method checks exact equality of the underlying graph
representation, not mathematical equality which involves graph isomorphism.

See also: `is_permuted_equal`
"""
function Base.:(==)(d1::WiringDiagram, d2::WiringDiagram)
  (input_ports(d1) == input_ports(d2) && output_ports(d1) == output_ports(d2) &&
   input_id(d1) == input_id(d2) && output_id(d1) == output_id(d2) &&
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

function Base.show(io::IO, diagram::WiringDiagram)
  sshowcompact = x -> sprint(show, x, context=:compact => true)
  print(io, "WiringDiagram(")
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

# Low-level graph interface
###########################

""" Create wiring diagram with a single box connected to outer ports.
"""
function to_wiring_diagram(box::AbstractBox)
  inputs, outputs = input_ports(box), output_ports(box)
  d = WiringDiagram(inputs, outputs)
  v = add_box!(d, box)
  add_wires!(d, ((input_id(d),i) => (v,i) for i in eachindex(inputs)))
  add_wires!(d, ((v,i) => (output_id(d),i) for i in eachindex(outputs)))
  return d
end

# Basic accessors.

box(f::WiringDiagram, v::Int) = get_prop(f.graph, v, :box)
boxes(f::WiringDiagram) = AbstractBox[ box(f,v) for v in box_ids(f) ]
nboxes(f::WiringDiagram) = nv(graph(f)) - 2

function box_ids(f::WiringDiagram)
  skip = (input_id(f), output_id(f))
  Int[ v for v in 1:nv(graph(f)) if !(v in skip) ]
end

function wires(f::WiringDiagram, edge::Edge)
  if has_edge(f.graph, edge)
    Wire[ from_edge_data(data, edge) for data in get_prop(f.graph,edge,:wires) ]
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
  @assert !(v in (input_id(f), output_id(f)))
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
    add_edge!(f.graph, src(edge), dst(edge), :wires, WireEdgeData[])
  end
  push!(get_prop(f.graph, edge, :wires), to_edge_data(wire))
end
add_wire!(f::WiringDiagram, pair::Pair) = add_wire!(f, Wire(pair))

function add_wires!(f::WiringDiagram, wires)
  for wire in wires
    add_wire!(f, wire)
  end
end

function rem_wire!(f::WiringDiagram, wire::Wire)
  edge = Edge(wire.source.box, wire.target.box)
  edge_data = to_edge_data(wire)
  wires = get_prop(f.graph, edge, :wires)
  deleteat!(wires, findlast(d -> d == edge_data, wires))
  if isempty(wires)
    rem_edge!(f.graph, edge)
  end
end
rem_wire!(f::WiringDiagram, pair::Pair) = rem_wire!(f, Wire(pair))

function rem_wires!(f::WiringDiagram, src::Int, tgt::Int)
  rem_edge!(f.graph, Edge(src, tgt))
end

""" Check compatibility of source and target ports.

Throws a `PortValueError` when the ports are incompatible. The default
implementation of this method is a no-op.
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

# Substitution and encapulsation
################################

# Substition.

""" Substitute a wiring diagram for a vertex.

This operation is the operadic composition of wiring diagrams.
"""
function substitute!(d::WiringDiagram, v::Int, sub::WiringDiagram)
  _substitute_insert!(d, v, sub)
  rem_box!(d, v)
  return d
end
function substitute!(d::WiringDiagram, v::Int)
  substitute!(d, v, box(d,v)::WiringDiagram)
end

""" Simultaneous substitution of wiring diagrams for vertices.
"""
function substitute!(d::WiringDiagram, vs::Vector{Int}, subs::Vector{WiringDiagram})
  for (v,sub) in zip(vs, subs)
    _substitute_insert!(d, v, sub)
  end
  rem_boxes!(d, vs)
  return d
end
function substitute!(d::WiringDiagram, vs::Vector{Int})
  substitute!(d, vs, WiringDiagram[ box(d,v) for v in vs ])
end

""" The insertion phase of a substitution operation.
"""
function _substitute_insert!(d::WiringDiagram, v::Int, sub::WiringDiagram)
  # Add new boxes from sub-diagram.
  sub_map = Dict{Int,Int}()
  for u in box_ids(sub)
    sub_map[u] = add_box!(d, box(sub,u))
  end
  
  # Add new wires from sub-diagram.
  for wire in wires(sub)
    src = get(sub_map, wire.source.box, 0)
    tgt = get(sub_map, wire.target.box, 0)
    
    # Special case: wire from input port to output port.
    if wire.source.box == input_id(sub) && wire.target.box == output_id(sub)
      for in_wire in in_wires(d, v, wire.source.port)
        for out_wire in out_wires(d, v, wire.target.port)
          add_wire!(d, Wire(in_wire.source, out_wire.target))
        end
      end
    # Special case: wire from input port to internal box.
    elseif wire.source.box == input_id(sub)
      for in_wire in in_wires(d, v, wire.source.port)
        add_wire!(d, Wire(in_wire.source, set_box(wire.target, tgt)))
      end  
    # Special case: wire from internal box to output port.
    elseif wire.target.box == output_id(sub)
      for out_wire in out_wires(d, v, wire.target.port)
        add_wire!(d, Wire(set_box(wire.source, src), out_wire.target))
      end
    # Default case: wire between two internal boxes.
    else
      add_wire!(d, Wire(set_box(wire.source, src), set_box(wire.target, tgt)))
    end
  end
  return d
end

# Encapsulation.

""" Encapsulate multiple boxes within a single sub wiring diagram.

This operation is a (one-sided) inverse to subsitution (see `substitute!`).
"""
function encapsulate!(d::WiringDiagram, vs::Vector{Int};
                      discard_boxes::Bool=false, value::Any=nothing)
  encapsulate!(d, [vs]; discard_boxes=discard_boxes, values=[value])
end

""" Simultaneous encapsulation of boxes.
"""
function encapsulate!(d::WiringDiagram, vss::Vector{Vector{Int}};
                      discard_boxes::Bool=false, values::Union{Nothing,Vector}=nothing)
  if any(isempty(vs) for vs in vss)
    error("Cannot encapsulate an empty set of boxes")
  end
  if isnothing(values)
    values = repeat([nothing], length(vss))
  end
  encapsulate_insert! = discard_boxes ? _encapsulate_in_box! : _encapsulate_in_diagram!
  for (vs, value) in zip(vss, values)
    encapsulate_insert!(d, vs, value)
  end
  rem_boxes!(d, vcat(vss...))
  return d
end
  
function _encapsulate_in_diagram!(d::WiringDiagram, vs::Vector{Int}, value::Any)
  # Create ports for encapsulating box.
  sub_vertex = nv(graph(d)) + 1
  inputs, outputs, port_map, sub_port_map =
    encapsulated_ports(d, vs, sub_vertex)
  
  # Add encapsulating diagram to original diagram.
  sub = WiringDiagram(value, inputs, outputs)
  @assert add_box!(d, sub) == sub_vertex
  
  # Add boxes to encapsulating diagram.
  vertex_map = Dict{Int,Int}((v => add_box!(sub, box(d, v)) for v in vs))
  
  # Add wires to original and encapsulating diagram.
  consumed = Set()
  for v in vs
    for wire in wires(d, v)
      # Check if wire has already been processed.
      src, tgt = wire.source, wire.target
      if src.box in consumed || tgt.box in consumed; continue end
      
      # Case 1: Add wire inside encapsulating diagram.
      if haskey(vertex_map, src.box) && haskey(vertex_map, tgt.box)
        add_wire!(sub, Wire(
          set_box(src, vertex_map[src.box]),
          set_box(tgt, vertex_map[tgt.box])
        ))
      
      # Case 2: Add wire from encapsulating box to another box.
      elseif haskey(vertex_map, src.box)
        add_wire!(sub, Wire(
          set_box(src, vertex_map[src.box]),
          Port(output_id(sub), InputPort, sub_port_map[src])
        ))
        if haskey(port_map, src)
          add_wire!(d, Wire(port_map[src], tgt))
        end
      
      # Case 3: Add wire to encapsulating box from another box.
      elseif haskey(vertex_map, tgt.box)
        if haskey(port_map, tgt)
          add_wire!(d, Wire(src, port_map[tgt]))
        end
        add_wire!(sub, Wire(
          Port(input_id(sub), OutputPort, sub_port_map[tgt]),
          set_box(tgt, vertex_map[tgt.box])
        ))
      end
    end
    push!(consumed, v)
  end
  return d
end

function _encapsulate_in_box!(d::WiringDiagram, vs::Vector{Int}, value::Any)
  # Create ports for encapsulating box.
  sub_vertex = nv(graph(d)) + 1
  inputs, outputs, port_map, _ = encapsulated_ports(d, vs, sub_vertex)
  
  # Add encapsulating box to original diagram.
  sub = Box(value, inputs, outputs)
  @assert add_box!(d, sub) == sub_vertex
  
  # Add wires to original and encapsulating diagram.
  vertex_set = Set(vs)
  consumed = Set()
  for v in vs
    for wire in wires(d, v)
      # Check if wire has already been processed.
      src, tgt = wire.source, wire.target
      if src.box in consumed || tgt.box in consumed; continue end
      
      # Case 1: Add wire from encapsulating box to another box.
      if haskey(port_map, src) && !(tgt.box in vertex_set)
        add_wire!(d, Wire(port_map[src], tgt))
      
      # Case 2: Add wire to encapsulating box from another box.
      elseif !(src.box in vertex_set) && haskey(port_map, tgt)
        add_wire!(d, Wire(src, port_map[tgt]))
      end
    end
    push!(consumed, v)
  end
  return d
end

""" Create input and output ports for encapsulating box.

Any port of the boxes `vs` that has an incoming (resp. outgoing) wire
from a box outside of `vs` will become an input (resp. output) port of the
encapsulating box.

A set of box ports connected to the same (set of) outside ports will be
simplified into a single port of the encapsulating box. This simplification
is only relevant when duplication or merging is used, as in a cartesian or
cocartesian category.
"""
function encapsulated_ports(d::WiringDiagram, vs::Vector{Int}, subv::Int)
  inputs, outputs = [], []
  outer_port_map = Dict{Port,Port}()
  inner_port_map = Dict{Port,Int}()
  neighbor_map = Dict{Tuple{Set{Port},Any},Int}()

  vertex_set = Set(vs)
  for v in vs
    # Add ports for incoming wires, preserving port order.
    for port in eachindex(input_ports(box(d, v)))
      tgt = Port(v, InputPort, port)
      srcs = Set(wire.source for wire in in_wires(d, tgt)
                 if !(wire.source.box in vertex_set))
      if !isempty(srcs)
        value = port_value(d, tgt)
        inner_port_map[tgt] = get!(neighbor_map, (srcs, value)) do
          push!(inputs, value)
          (outer_port_map[tgt] = Port(subv, InputPort, length(inputs))).port
        end
      end
    end
    
    # Add ports for outgoing wires, preserving port order.
    for port in eachindex(output_ports(box(d, v)))
      src = Port(v, OutputPort, port)
      tgts = Set(wire.target for wire in out_wires(d, src)
                 if !(wire.target.box in vertex_set))
      if !isempty(tgts)
        value = port_value(d, src)
        inner_port_map[src] = get!(neighbor_map, (tgts, value)) do
          push!(outputs, value)
          (outer_port_map[src] = Port(subv, OutputPort, length(outputs))).port
        end
      end
    end
  end
  
  # Return input and output port values with the tightest possible types.
  inputs, outputs = [ x for x in inputs ], [ x for x in outputs ]
  (inputs, outputs, outer_port_map, inner_port_map)
end

# High-level categorical interface
##################################

""" Create box for a morphism generator.
"""
function Box(expr::HomExpr{:generator})
  Box(first(expr), collect_values(dom(expr)), collect_values(codom(expr)))
end
add_box!(f::WiringDiagram, expr::HomExpr) = add_box!(f, Box(expr))

""" Create empty wiring diagram with given domain and codomain objects.
"""
function WiringDiagram(inputs::ObExpr, outputs::ObExpr)
  WiringDiagram(collect_values(inputs), collect_values(outputs))
end

""" Wiring diagram as *monoidal category with diagonals and codiagonals*.
"""
@instance MonoidalCategoryWithBidiagonals(Ports, WiringDiagram) begin
  dom(f::WiringDiagram) = Ports(f.input_ports)
  codom(f::WiringDiagram) = Ports(f.output_ports)
  
  function id(A::Ports)
    f = WiringDiagram(A, A)
    add_wires!(f, ((input_id(f),i) => (output_id(f),i) for i in eachindex(A)))
    return f
  end
  
  function compose(f::WiringDiagram, g::WiringDiagram)
    # Check only that f and g have the same number of ports.
    # The port types will be checked when the wires are added.
    if length(codom(f)) != length(dom(g))
      error("Incompatible domains $(codom(f)) and $(dom(g))")
    end
    
    h = WiringDiagram(dom(f), codom(g))
    fv = add_box!(h, f)
    gv = add_box!(h, g)
    add_wires!(h, ((input_id(h),i) => (fv,i) for i in eachindex(dom(f))))
    add_wires!(h, ((fv,i) => (gv,i) for i in eachindex(codom(f))))
    add_wires!(h, ((gv,i) => (output_id(h),i) for i in eachindex(codom(g))))
    substitute!(h, [fv,gv])
    return h
  end
  
  otimes(A::Ports, B::Ports) = Ports([A.ports; B.ports])
  munit(::Type{Ports}) = Ports([])
  
  function otimes(f::WiringDiagram, g::WiringDiagram)
    h = WiringDiagram(otimes(dom(f),dom(g)), otimes(codom(f),codom(g)))
    m, n = length(dom(f)), length(codom(f))
    fv = add_box!(h, f)
    gv = add_box!(h, g)
    add_wires!(h, (input_id(h),i) => (fv,i) for i in eachindex(dom(f)))
    add_wires!(h, (input_id(h),i+m) => (gv,i) for i in eachindex(dom(g)))
    add_wires!(h, (fv,i) => (output_id(h),i) for i in eachindex(codom(f)))
    add_wires!(h, (gv,i) => (output_id(h),i+n) for i in eachindex(codom(g)))
    substitute!(h, [fv,gv])
    return h
  end
  
  function braid(A::Ports, B::Ports)
    h = WiringDiagram(otimes(A,B), otimes(B,A))
    m, n = length(A), length(B)
    add_wires!(h, ((input_id(h),i) => (output_id(h),i+n) for i in 1:m))
    add_wires!(h, ((input_id(h),i+m) => (output_id(h),i) for i in 1:n))
    return h
  end

  mcopy(A::Ports) = mcopy(A, 2)
  mmerge(A::Ports) = mmerge(A, 2)
  delete(A::Ports) = WiringDiagram(A, munit(Ports))
  create(A::Ports) = WiringDiagram(munit(Ports), A)
end

function permute(A::Ports, σ::Vector{Int}; inverse::Bool=false)
  @assert length(A) == length(σ)
  B = Ports([ A.ports[σ[i]] for i in eachindex(σ) ])
  if inverse
    f = WiringDiagram(B, A)
    add_wires!(f, ((input_id(f),σ[i]) => (output_id(f),i) for i in eachindex(σ)))
    return f
  else
    f = WiringDiagram(A, B)
    add_wires!(f, ((input_id(f),i) => (output_id(f),σ[i]) for i in eachindex(σ)))
    return f
  end
end

function mcopy(A::Ports, n::Int)::WiringDiagram
  f = WiringDiagram(A, otimes([A for j in 1:n]))
  m = length(A)
  for j in 1:n
    add_wires!(f, ((input_id(f),i) => (output_id(f),i+m*(j-1)) for i in 1:m))
  end
  return f
end

function mmerge(A::Ports, n::Int)::WiringDiagram
  f = WiringDiagram(otimes([A for j in 1:n]), A)
  m = length(A)
  for j in 1:n
    add_wires!(f, ((input_id(f),i+m*(j-1)) => (output_id(f),i) for i in 1:m))
  end
  return f
end

function collect_values(ob::ObExpr)::Vector
  exprs = collect(ob)
  @assert all(head(expr) == :generator for expr in exprs)
  return map(first, exprs)
end

end
