""" Data structure for (directed) wiring diagrams, aka string diagrams.

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
module DirectedWiringDiagrams
export AbstractBox, Box, WiringDiagram, SchWiringDiagram,
  SchTypedWiringDiagram, SchAttributedWiringDiagram,
  Wire, Port, PortKind, InputPort, OutputPort, input_ports, output_ports,
  set_input_ports!, set_output_ports!, add_input_ports!, add_output_ports!,
  input_id, output_id, outer_ids, boxes, box_ids, nboxes, nwires, box, wires,
  has_wire, graph, internal_graph,
  add_box!, add_boxes!, add_wire!, add_wires!, rem_box!, rem_boxes!, rem_wire!,
  rem_wires!, port_value, validate_ports, is_isomorphic,
  all_neighbors, neighbors, outneighbors, inneighbors, in_wires, out_wires,
  singleton_diagram, induced_subdiagram, encapsulated_subdiagram,
  ocompose, substitute, encapsulate

using StructEquality

using ...Present, ...Graphs.BasicGraphs, ...CategoricalAlgebra.CSets
import ...CategoricalAlgebra.CSets: is_isomorphic
import ...CategoricalAlgebra.FinCats: graph
import ...Graphs: all_neighbors, neighbors, outneighbors, inneighbors

# Data types
############

""" Kind of port: input or output.
"""
@enum PortKind InputPort OutputPort

""" A port on a box to which wires can be connected.
"""
@struct_hash_equal struct Port
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
@struct_hash_equal struct Wire{Value}
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

""" Base type for any box (node) in a wiring diagram.

This type represents an arbitrary black box with inputs and outputs.
"""
abstract type AbstractBox end

input_ports(box::AbstractBox) = box.input_ports
output_ports(box::AbstractBox) = box.output_ports
value(b::AbstractBox) = b.value

""" An atomic box in a wiring diagram.

These boxes have no internal structure.
"""
@struct_hash_equal struct Box{Value} <: AbstractBox
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

@present SchWiringDiagram(FreeSchema) begin
  Box::Ob
  (InPort, OutPort, OuterInPort, OuterOutPort)::Ob
  (Wire, InWire, OutWire, PassWire)::Ob
  
  src::Hom(Wire, OutPort)
  tgt::Hom(Wire, InPort)
  in_src::Hom(InWire, OuterInPort)
  in_tgt::Hom(InWire, InPort)
  out_src::Hom(OutWire, OutPort)
  out_tgt::Hom(OutWire, OuterOutPort)
  pass_src::Hom(PassWire, OuterInPort)
  pass_tgt::Hom(PassWire, OuterOutPort)

  in_port_box::Hom(InPort, Box)
  out_port_box::Hom(OutPort, Box)
end

@abstract_acset_type AbstractWiringDiagram <: AbstractGraph

@present SchTypedWiringDiagram <: SchWiringDiagram begin
  PortValue::AttrType
  in_port_type::Attr(InPort, PortValue)
  out_port_type::Attr(OutPort, PortValue)
  outer_in_port_type::Attr(OuterInPort, PortValue)
  outer_out_port_type::Attr(OuterOutPort, PortValue)
end

@present SchAttributedWiringDiagram <: SchTypedWiringDiagram begin
  WireValue::AttrType
  BoxValue::AttrType
  BoxType::AttrType

  value::Attr(Box, BoxValue)
  box_type::Attr(Box, BoxType)
  wire_value::Attr(Wire, WireValue)
  in_wire_value::Attr(InWire, WireValue)
  out_wire_value::Attr(OutWire, WireValue)
  pass_wire_value::Attr(PassWire, WireValue)
end

@acset_type WiringDiagramACSet(SchAttributedWiringDiagram,
  index=[:src, :tgt, :in_src, :in_tgt, :out_src, :out_tgt, :pass_src, :pass_tgt]) <: AbstractWiringDiagram

""" A directed wiring diagram, also known as a string diagram.

The wiring diagram is implemented using the following internal data structure.
The "skeleton" of the diagram is an instance of `Catlab.Graphs.AbstractGraph`: a
directed multigraph whose vertices correspond to boxes and whose edges
correspond to wires. There are two special vertices, accessible via `input_id`
and `output_id`, that represent the input and output ports of the outer box.
"""

mutable struct WiringDiagram{Theory, PortValue, WireValue, BoxValue} <: AbstractBox
  diagram::WiringDiagramACSet{PortValue, WireValue, Union{BoxValue, AbstractBox}, DataType}
  value::Any

  function WiringDiagram{T, PortValue, WireValue, BoxValue}(value, inputs::Vector, outputs::Vector) where {T, PortValue, WireValue, BoxValue}
    diagram = WiringDiagramACSet{PortValue, WireValue, Union{BoxValue, AbstractBox}, DataType}()
    f = new{T, PortValue, WireValue, BoxValue}(diagram, value)
    add_parts!(diagram, :OuterInPort, length(inputs),   outer_in_port_type=inputs)
    add_parts!(diagram, :OuterOutPort, length(outputs), outer_out_port_type=outputs)
    return f
  end
  function WiringDiagram(f::WiringDiagram{T, PortValue, WireValue, BoxValue}) where {T, PortValue, WireValue, BoxValue}
    # Copy constructor for shallow copy
    new{T, PortValue, WireValue, BoxValue}(copy(f.diagram), f.value)
  end
  function WiringDiagram{T, PortValue, WireValue, BoxValue}(
      diagram::WiringDiagramACSet{PortValue, WireValue, Union{BoxValue, AbstractBox}, DataType},
      value) where {T, PortValue, WireValue, BoxValue}
    new{T, PortValue, WireValue, BoxValue}(diagram, value)
  end
end

function WiringDiagram{T, PortValue, WireValue, BoxValue}(inputs::Vector, outputs::Vector) where {T, PortValue, WireValue, BoxValue}
  WiringDiagram{T, PortValue, WireValue, BoxValue}(nothing, inputs, outputs)
end
WiringDiagram(args...) = WiringDiagram{Any, Any, Any, Any}(args...)
WiringDiagram{T}(args...) where T = WiringDiagram{T, Any, Any, Any}(args...)

input_id(::WiringDiagram) = -2
output_id(::WiringDiagram) = -1
outer_ids(::WiringDiagram) = (-2,-1)

""" Are the two wiring diagrams equal?

**Warning**: This method checks equality of the underlying C-set representation.
Use [`is_isomorphic`](@ref) to check isomorphism of wiring diagrams.
"""
function Base.:(==)(d1::WiringDiagram, d2::WiringDiagram)
  (input_ports(d1) == input_ports(d2) &&
   output_ports(d1) == output_ports(d2) && d1.value == d2.value &&
   boxes(d1) == boxes(d2) && sort!(wires(d1)) == sort!(wires(d2)))
end

function is_isomorphic(d1::WiringDiagram, d2::WiringDiagram)
  d1.value == d2.value && is_isomorphic(d1.diagram, d2.diagram)
end

Base.copy(d::WiringDiagram) = begin
  # WARNING WARNING WARNING
  # IF YOU WANT TO UNDERSTAND WHY THIS HACK WAS NECESSARY, YOU MUST BE PREPARED
  # TO LOSE YOUR SANITY
  #
  #
  #
  # OK, READY?
  #
  # THE copy METHOD FOR ACSETS BREAKS THE JULIA COMPILER WHEN THE TYPE OF THE
  # ARGUMENT IS *PARTIALLY* INFERRED; FULL INFERENCE AND FULL DYNAMIC DISPATCH
  # BOTH WORK FINE. SO HERE WE ARE FORGETTING OUR PARTIAL KNOWLEDGE OF THE TYPE
  # OF THE ACSET SO THAT FULL DYNAMIC DISPATCH IS INVOKED. THIS IS ONLY
  # NECESSARY FOR JULIA 1.6; 1.7 AND ABOVE DON'T HAVE THIS PROBLEM
  diag = (Any[d.diagram])[1]
  WiringDiagram(copy(diag), d.value)
end

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

@present SchWiringDiagramGraph <: SchGraph begin
  ID::AttrType
  box::Attr(V,ID)
  wire::Attr(E,ID)
end

""" Graph underlying a directed wiring diagram.
"""
@acset_type WiringDiagramGraphACSet(SchWiringDiagramGraph,
  index=[:src, :tgt], unique_index=[:box]) <: AbstractGraph
const WiringDiagramGraph = WiringDiagramGraphACSet{Int}

# Imperative interface
######################

# Basic accessors.

function box(f::WiringDiagram, b::Int)
  b ∉ outer_ids(f) || return nothing
  value = subpart(f.diagram, b, :value)
  if value isa AbstractBox
    value
  else
    BoxType = subpart(f.diagram, b, :box_type)
    BoxType(value, input_ports(f, b), output_ports(f, b))
  end
end

boxes(f::WiringDiagram) = map(b -> box(f, b), box_ids(f))
nboxes(f::WiringDiagram) = nparts(f.diagram, :Box)
box_ids(f::WiringDiagram) = collect(parts(f.diagram, :Box))

src_box(f::WiringDiagram, w::Int) = subpart(f.diagram, w, [:src, :out_port_box])
tgt_box(f::WiringDiagram, w::Int) = subpart(f.diagram, w, [:tgt, :in_port_box])
in_tgt_box(f::WiringDiagram, w::Int) = subpart(f.diagram, w, [:in_tgt, :in_port_box])
out_src_box(f::WiringDiagram, w::Int) = subpart(f.diagram, w, [:out_src, :out_port_box])

local_in_port_id(f::WiringDiagram, b::Int, p::Int) =
  searchsortedfirst(incident(f.diagram, b, :in_port_box), p)
local_out_port_id(f::WiringDiagram, b::Int, p::Int) =
  searchsortedfirst(incident(f.diagram, b, :out_port_box), p)

in_port_id(f::WiringDiagram, b::Int, p::Int) = incident(f.diagram, b, :in_port_box)[p]
out_port_id(f::WiringDiagram, b::Int, p::Int) = incident(f.diagram, b, :out_port_box)[p]
in_port_id(f::WiringDiagram, p::Port) = in_port_id(f, p.box, p.port)
out_port_id(f::WiringDiagram, p::Port) = out_port_id(f, p.box, p.port)

@inline Wire(f::WiringDiagram, type::Symbol, w::Int) = Wire(f, Val{type}, w)

function Wire(f::WiringDiagram, ::Type{Val{:PassWire}}, w::Int)
  Wire(subpart(f.diagram, w, :pass_wire_value),
       (input_id(f), subpart(f.diagram, w, :pass_src)) =>
       (output_id(f), subpart(f.diagram, w, :pass_tgt)))
end

function Wire(f::WiringDiagram, ::Type{Val{:InWire}}, w::Int)
  Wire(subpart(f.diagram, w, :in_wire_value),
       (input_id(f),
        subpart(f.diagram, w, :in_src)) => 
       (in_tgt_box(f,w),
        local_in_port_id(f, in_tgt_box(f,w), subpart(f.diagram, w, :in_tgt))))
end

function Wire(f::WiringDiagram, ::Type{Val{:OutWire}}, w::Int)
  Wire(subpart(f.diagram, w, :out_wire_value),
       (out_src_box(f,w),
        local_out_port_id(f, out_src_box(f,w), subpart(f.diagram, w, :out_src))) =>
       (output_id(f),
        subpart(f.diagram, w, :out_tgt)))
end

function Wire(f::WiringDiagram, ::Type{Val{:Wire}}, w::Int)
  Wire(subpart(f.diagram, w, :wire_value),
       (src_box(f,w),
        local_out_port_id(f, src_box(f,w), subpart(f.diagram, w, :src))) =>
       (tgt_box(f,w),
        local_in_port_id(f, tgt_box(f,w), subpart(f.diagram, w, :tgt))))
end

function wires(f::WiringDiagram, src::Int, tgt::Int)
  if src == input_id(f) && tgt == output_id(f)
    [Wire(f, :PassWire, w) for w in parts(f.diagram, :PassWire)]
  elseif src == input_id(f)
    [Wire(f, :InWire, w)
     for w in incident(f.diagram, tgt, [:in_tgt, :in_port_box])]
  elseif tgt == output_id(f)
    [Wire(f, :OutWire, w)
     for w in incident(f.diagram, src, [:out_src, :out_port_box])]
  else
    [Wire(f, :Wire, w) for w in incident(f.diagram, src, [:src, :out_port_box])
     if tgt_box(f,w) == tgt]
  end
end

wires(f::WiringDiagram, type::Symbol) =
  [ Wire(f, type, w) for w in parts(f.diagram, type) ]
wires(f::WiringDiagram) = vcat(wires(f, :PassWire), wires(f, :InWire),
                               wires(f, :Wire), wires(f, :OutWire))

function nwires(f::WiringDiagram, src::Int, tgt::Int)
  if src == input_id(f) && tgt == output_id(f)
    nparts(f.diagram, :PassWire)
  elseif src == input_id(f)
    length(incident(f.diagram, tgt, [:in_tgt, :in_port_box]))
  elseif tgt == output_id(f)
    length(incident(f.diagram, src, [:out_src, :out_port_box]))
  else
    count(w -> tgt_box(f,w) == tgt,
          incident(f.diagram, src, [:src, :out_port_box]))
  end
end

nwires(f::WiringDiagram, type::Symbol) = nparts(f.diagram, type)
nwires(f::WiringDiagram) = (nwires(f, :PassWire) + nwires(f, :InWire) +
                            nwires(f, :Wire) + nwires(f, :OutWire))

has_wire(f::WiringDiagram, src::Int, tgt::Int) = nwires(f, src, tgt) > 0
has_wire(f::WiringDiagram, wire::Wire) =
  wire in wires(f, wire.source.box, wire.target.box)
has_wire(f::WiringDiagram, pair::Pair) = has_wire(f, Wire(pair))

input_ports(f::WiringDiagram) = subpart(f.diagram, :outer_in_port_type) |> collect
output_ports(f::WiringDiagram) = subpart(f.diagram, :outer_out_port_type) |> collect

set_input_ports!(f::WiringDiagram, input_ports::AbstractVector) =
  set_subpart!(f.diagram, :outer_in_port_type, input_ports)
set_output_ports!(f::WiringDiagram, output_ports::AbstractVector) =
  set_subpart!(f.diagram, :outer_out_port_type, output_ports)
add_input_ports!(f::WiringDiagram, input_ports::AbstractVector) =
  add_parts!(f.diagram, :OuterInPort, length(input_ports),
             outer_in_port_type = input_ports)
add_output_ports!(f::WiringDiagram, output_ports::AbstractVector) =
  add_parts!(f.diagram, :OuterOutPort, length(output_ports),
             outer_out_port_type = output_ports)

function input_ports(f::WiringDiagram, b::Int)
  if b == input_id(f)
    error("Input vertex does not have input ports within wiring diagram")
  elseif b == output_id(f)
    output_ports(f)
  else
    subpart(f.diagram, incident(f.diagram, b, :in_port_box), :in_port_type) |>
      collect # Copy for backwards compatibilty.
  end
end

function output_ports(f::WiringDiagram, b::Int)
  if b == input_id(f)
    input_ports(f)
  elseif b == output_id(f)
    error("Output vertex does not have output ports within wiring diagram")
  else
    subpart(f.diagram, incident(f.diagram, b, :out_port_box), :out_port_type) |>
      collect # Copy for backwards compatibilty.
  end
end

function port_value(f::WiringDiagram, port::Port)
  if port.box == input_id(f)
    subpart(f.diagram, port.port, :outer_in_port_type)
  elseif port.box == output_id(f)
    subpart(f.diagram, port.port, :outer_out_port_type)
  else
    port_id   = port.kind == InputPort ? in_port_id : out_port_id
    type_expr = port.kind == InputPort ? :in_port_type : :out_port_type
    subpart(f.diagram, port_id(f, port), type_expr)
  end
end

# Graph mutation.

function add_box!(f::WiringDiagram, box::B) where B <: AbstractBox
  b = add_part!(f.diagram, :Box,
                box_type=B, value=B <: WiringDiagram ? box : value(box))
  add_parts!(f.diagram, :InPort, length(input_ports(box)),
             in_port_box=b, in_port_type=input_ports(box))
  add_parts!(f.diagram, :OutPort, length(output_ports(box)),
             out_port_box=b, out_port_type=output_ports(box))
  return b
end 

function add_boxes!(f::WiringDiagram, boxes)
  firstbox = nboxes(f) + 1
  for box in boxes
    add_box!(f, box)
  end
  lastbox = nboxes(f)
  return firstbox:lastbox
end

function rem_box!(f::WiringDiagram, b::Int)
  rem_boxes!(f, b:b)
end

function rem_boxes!(f::WiringDiagram, bs::AbstractVector{Int})
  @assert all(1 <= b <= nboxes(f) for b in bs)

  # Remove associated wires.
  rem_parts!(f.diagram, :InWire, incident_reduce(f.diagram, bs, [:in_tgt, :in_port_box]))
  rem_parts!(f.diagram, :OutWire, incident_reduce(f.diagram, bs, [:out_src, :out_port_box]))
  rem_parts!(f.diagram, :Wire, incident_reduce(f.diagram, bs, [:tgt, :in_port_box]))
  rem_parts!(f.diagram, :Wire, incident_reduce(f.diagram, bs, [:src, :out_port_box]))

  # Remove associated ports.
  rem_parts!(f.diagram, :InPort, incident_reduce(f.diagram, bs, [:in_port_box]))
  rem_parts!(f.diagram, :OutPort, incident_reduce(f.diagram, bs, [:out_port_box]))

  rem_parts!(f.diagram, :Box, bs)
end
rem_boxes!(f::WiringDiagram, bs) = rem_boxes!(f, collect(Int, bs))

incident_reduce(args...) = sort(reduce(vcat, incident(args...), init=Int[]))

function add_wire!(f::WiringDiagram, wire::Wire)
  validate_ports(port_value(f, wire.source), port_value(f, wire.target))
  if wire.source.box == input_id(f) && wire.target.box == output_id(f)
    add_part!(f.diagram, :PassWire, pass_wire_value = wire.value,
              pass_src = wire.source.port,
              pass_tgt = wire.target.port)
  elseif wire.source.box == input_id(f)
    add_part!(f.diagram, :InWire, in_wire_value = wire.value,
              in_src = wire.source.port,
              in_tgt = in_port_id(f, wire.target))
  elseif wire.target.box == output_id(f)
    add_part!(f.diagram, :OutWire, out_wire_value=wire.value,
              out_src = out_port_id(f, wire.source),
              out_tgt = wire.target.port)
  else
    add_part!(f.diagram, :Wire, wire_value=wire.value,
              src = out_port_id(f, wire.source),
              tgt = in_port_id(f, wire.target))
  end
end
add_wire!(f::WiringDiagram, pair::Pair) = add_wire!(f, Wire(pair))

function add_wires!(f::WiringDiagram, wires)
  for wire in wires
    add_wire!(f, wire)
  end
end

function rem_wire!(f::WiringDiagram, wire::Wire)
  if wire.source.box == input_id(f) && wire.target.box == output_id(f)
    for w in parts(f.diagram, :PassWire)
      subpart(f.diagram, w, :pass_wire_value) == wire.value &&
        subpart(f.diagram, w, :pass_src) == wire.source.port &&
        subpart(f.diagram, w, :pass_tgt) == wire.target.port &&
        return rem_part!(f.diagram, :PassWire, w)
    end
  elseif wire.source.box == input_id(f)
    for w in incident(f.diagram, in_port_id(f, wire.target), :in_tgt)
      subpart(f.diagram, w, :in_wire_value) == wire.value &&
        return rem_part!(f.diagram, :InWire, w)
    end
  elseif wire.target.box == output_id(f)
    for w in incident(f.diagram, out_port_id(f, wire.source), :out_src)
      subpart(f.diagram, w, :out_wire_value) == wire.value &&
        return rem_part!(f.diagram, :OutWire, w)
    end
  else
    for w in incident(f.diagram, out_port_id(f, wire.source), :src)
      subpart(f.diagram, w, :tgt) == in_port_id(f, wire.target) &&
        subpart(f.diagram, w, :wire_value) == wire.value &&
        return rem_part!(f.diagram, :Wire, w)
    end
  end
  error("Wire $wire does not exist, so cannot be removed")
end
rem_wire!(f::WiringDiagram, pair::Pair) = rem_wire!(f, Wire(pair))

function rem_wires!(f::WiringDiagram, wires)
  for wire in wires
    rem_wire!(f, wire)
  end
end

function rem_wires!(f::WiringDiagram, src::Int, tgt::Int)
  if src == input_id(f) && tgt == output_id(f)
    rem_parts!(f.diagram, :PassWire, parts(f.diagram, :PassWire))
  elseif src == input_id(f) 
    rem_parts!(f.diagram, :InWire, incident(f.diagram, tgt, [:in_tgt, :in_port_box]))
  elseif tgt == output_id(f)
    rem_parts!(f.diagram, :OutWire, incident(f.diagram, src, [:out_src, :out_port_box]))
  else
    wires = filter(w -> tgt_box(f,w) == tgt,
                   incident(f.diagram, src, [:src, :out_port_box]))
    rem_parts!(f.diagram, :Wire, wires)
  end
end

function add_outer_in_port!(f::WiringDiagram, value)
  add_part!(f.diagram, :OuterInPort, outer_in_port_type=value)
end

function add_outer_out_port!(f::WiringDiagram, value)
  add_part!(f.diagram, :OuterOutPort, outer_out_port_type=value)
end

""" Check compatibility of source and target ports.

The default implementation is a no-op.
"""
function validate_ports(source_port, target_port) end

# Graph properties.

""" Graph underlying wiring diagram, with edges for internal wires only.
"""
function internal_graph(f::WiringDiagram)
  g = WiringDiagramGraph()
  add_parts!(g, :V, nparts(f.diagram, :Box), box = parts(f.diagram, :Box))
  add_parts!(g, :E, nparts(f.diagram, :Wire),
             src = subpart(f.diagram, [:src, :out_port_box]),
             tgt = subpart(f.diagram, [:tgt, :in_port_box]),
             wire = parts(f.diagram, :Wire))
  return g
end

""" Grapn underlying wiring diagram, including parts for noin-internal wires.

The graph has two special vertices representing the input and output boundaries
of the outer box.
"""
function graph(f::WiringDiagram)
  g = internal_graph(f)
  input, output = add_parts!(g, :V, 2, box = [input_id(f), output_id(f)])
  add_parts!(g, :E, nparts(f.diagram, :InWire),
             src = input,
             tgt = subpart(f.diagram, [:in_tgt, :in_port_box]),
             wire = parts(f.diagram, :InWire))
  add_parts!(g, :E, nparts(f.diagram, :OutWire),
             src = subpart(f.diagram, [:out_src, :out_port_box]),
             tgt = output,
             wire = parts(f.diagram, :OutWire))
  add_parts!(g, :E, nparts(f.diagram, :PassWire),
             src = input, tgt = output,
             wire = parts(f.diagram, :PassWire))
  return g
end

function outneighbors(f::WiringDiagram, b::Int)
  if b == input_id(f)
    vcat(subpart(f.diagram, [:in_tgt, :in_port_box]),
         fill(output_id(f), nwires(f, :PassWire)))
  elseif b == output_id(f)
    Int[]
  else
    vcat(subpart(f.diagram, incident(f.diagram, b, [:src, :out_port_box]),
                 [:tgt, :in_port_box]),
         fill(output_id(f),
              length(incident(f.diagram, b, [:out_src, :out_port_box]))))
  end
end

function inneighbors(f::WiringDiagram, b::Int)
  if b == input_id(f)
    Int[]
  elseif b == output_id(f)
    vcat(fill(input_id(f), nwires(f, :PassWire)),
         subpart(f.diagram, [:out_src, :out_port_box]))
  else
    vcat(fill(input_id(f),
              length(incident(f.diagram, b, [:in_tgt, :in_port_box]))),
         subpart(f.diagram, incident(f.diagram, b, [:tgt, :in_port_box]),
                 [:src, :out_port_box]))
  end
end

neighbors(f::WiringDiagram, b::Int) = outneighbors(f, b)
all_neighbors(f::WiringDiagram, b::Int) = 
  Iterators.flatten((inneighbors(f, b), outneighbors(f, b)))

""" Get all wires coming into or out of the box.
"""
function wires(f::WiringDiagram, b::Int)
  vcat(in_wires(f,b), out_wires(f,b))
end

""" Get all wires coming into the box.
"""
function in_wires(f::WiringDiagram, b::Int)
  if b == input_id(f)
    Wire[]
  elseif b == output_id(f)
    vcat(wires(f, :PassWire), wires(f, :OutWire))
  else
    vcat([Wire(f, :Wire, w) for w in incident(f.diagram, b, [:tgt, :in_port_box])],
         [Wire(f, :InWire, w) for w in incident(f.diagram, b, [:in_tgt, :in_port_box])])
  end
end

""" Get all wires coming into the port.
"""
function in_wires(d::WiringDiagram, port::Port)
  filter(wire -> wire.target == port, in_wires(d, port.box))
end
function in_wires(d::WiringDiagram, v::Int, port::Int)
  in_wires(d, Port(v, InputPort, port))
end

""" Get all wires coming out of the box.
"""
function out_wires(f::WiringDiagram, b::Int)
  if b == input_id(f)
    vcat(wires(f, :PassWire), wires(f, :InWire))
  elseif b == output_id(f)
    return Wire[]
  else
    vcat([Wire(f, :Wire, w) for w in incident(f.diagram, b, [:src, :out_port_box])],
         [Wire(f, :OutWire, w) for w in incident(f.diagram, b, [:out_src, :out_port_box])])
  end
end

""" Get all wires coming out of the port.
"""
function out_wires(d::WiringDiagram, port::Port)
  filter(wire -> wire.source == port, out_wires(d, port.box))
end
function out_wires(d::WiringDiagram, v::Int, port::Int)
  out_wires(d, Port(v, OutputPort, port))
end

# Other constructors
#-------------------

""" Wiring diagram with a single box connected to the outer ports.
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

# Operadic interface
####################

""" Operadic composition of wiring diagrams.

This generic function has two different signatures, corresponding to the "full"
and "partial" notions of operadic composition (Yau, 2018, *Operads of Wiring
Diagrams*, Definitions 2.3 and 2.10).

This operation is a simple wrapper around [`substitute`](@ref).
"""
function ocompose(f::WiringDiagram, gs::Vector{<:WiringDiagram})
  @assert length(gs) == nboxes(f)
  substitute(f, box_ids(f), gs)
end
function ocompose(f::WiringDiagram, i::Int, g::WiringDiagram)
  @assert 1 <= i <= nboxes(f)
  substitute(f, box_ids(f)[i], g)
end

# Substitution
##############

""" Substitute wiring diagrams for boxes.

Performs one or more substitutions. When performing multiple substitutions, the
substitutions are simultaneous.

This operation implements the operadic composition of wiring diagrams, see also
[`ocompose`](@ref).
"""
function substitute(d::WiringDiagram; kw...)
  substitute(d, filter(v -> box(d,v) isa WiringDiagram, box_ids(d)); kw...)
end
function substitute(d::WiringDiagram, v::Int; kw...)
  substitute(d, v, box(d,v)::WiringDiagram; kw...)
end
function substitute(d::WiringDiagram, vs::AbstractVector{Int}; kw...)
  substitute(d, vs, WiringDiagram[ box(d,v) for v in vs ]; kw...)
end
function substitute(d::WiringDiagram, v::Int, sub::WiringDiagram; kw...)
  substitute(d, [v], [sub]; kw...)
end

function substitute(d::WD, vs::AbstractVector{Int}, subs::Vector{<:WiringDiagram};
                    merge_wire_values=default_merge_wire_values) where WD <: WiringDiagram
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
  result = WD(d.value, input_ports(d), output_ports(d))
  
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

This operation is a (one-sided) inverse to subsitution, see
[`substitute`](@ref).
"""
function encapsulate(d::WiringDiagram, vs::Vector{Int}; value=nothing, kw...)
  encapsulate(d, [vs]; values=[value], kw...)
end

function encapsulate(d::WD, vss::Vector{Vector{Int}}; discard_boxes::Bool=false,
                     make_box=Box, values=nothing) where WD <: WiringDiagram
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
  result = WD(d.value, input_ports(d), output_ports(d))
  
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
      merge!(port_map, Dict(port => Port(subv, at...)
                            for (port, at) in sub_map))
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
function encapsulated_subdiagram(d::WD, vs::Vector{Int}; discard_boxes::Bool=false,
                                 make_box=Box, value=nothing) where WD <: WiringDiagram
  # Add encapsulated box to new wiring diagram.
  inputs, outputs = [], []
  result = discard_boxes ? nothing : WD(value, inputs, outputs)
  vmap = if discard_boxes
    Dict(v => nothing for v in vs)
  else
    Dict(v => add_box!(result, box(d, v)) for v in vs)
  end
  
  # Process wires into, or out of, encapsulated boxes.
  port_map = Dict{Port,NamedTuple{(:kind,:port),Tuple{PortKind,Int}}}()
  inner_port_map = Dict{Tuple{Vector{Port},Any},Int}()
  for v in vs
    # Add input ports to encapsulating box and corresponding wire.
    for (port, value) in enumerate(input_ports(d, v))
      tgt = Port(v, InputPort, port)
      srcs = sort!([ wire.source for wire in in_wires(d, tgt)
                     if !haskey(vmap, wire.source.box) ])
      if isempty(srcs) continue end
      src = get!(inner_port_map, (srcs, value)) do
        p = discard_boxes ? length(push!(inputs, value)) : add_outer_in_port!(result, value)
        port_data = port_map[tgt] = (kind=InputPort, port=p)
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
        p = discard_boxes ? length(push!(outputs, value)) : add_outer_out_port!(result, value)
        port_data = port_map[src] = (kind=OutputPort, port=p)
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

  if discard_boxes
    result = make_box(value, inputs, outputs)
  end
  (result, port_map)
end

end
