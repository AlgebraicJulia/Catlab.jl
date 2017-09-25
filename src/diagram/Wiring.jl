""" Generic data structure for wiring diagrams (aka, string diagrams).

A (directed) wiring diagram consists of a collection of boxes with input and
output ports connected by wires. A box can be atomic (possessing no internal
structure) or can itself be a wiring diagram. Thus, wiring diagrams can be
nested recursively. Wiring diagrams are closely related to what the CS
literature calls "directed graphs with ports" or more simply "port graphs". The
main difference is that a wiring diagram has an "outer box": a wiring diagram
has its own ports that can be connected to the ports of its boxes.

Wiring diagrams are a graphical syntax for morphisms in a monoidal category.
As mathematical objects, they are intermediate between morphisms (viewed
abstractly) and expressions in the textual syntax: a single morphism may
correspond to many wiring diagrams, and a single wiring diagram may correspond
to many syntactic expressions. This module provides functions to translate
syntactic expressions to wiring diagrams (TODO: and back again?).

This module offers a generic data structure for wiring diagrams. Arbitrary data
can be attached to the boxes, ports, and wires of a wiring diagram. There is a
low-level interface for direct manipulation of boxes and wires and a high-level
interface based on the theory of symmetric monoidal categories. 

The wiring diagrams in this module are "abstract" in the sense that they cannot
be directly rendered as raster or vector graphics. However, they form a useful
intermediate representation that can be straightforwardly serialized to and from
GraphML or translated into Graphviz or other declarative diagram languages.
"""
module Wiring
export AbstractBox, Box, WiringDiagram, Wire, Ports, PortValueError, Port,
  PortKind, InputPort, OutputPort, input_ports, output_ports, port_value,
  input_id, output_id, boxes, box_ids, nboxes, nwires, box, wires, has_wire,
  graph, add_box!, add_boxes!, add_wire!, add_wires!, validate_ports,
  rem_box!, rem_boxes!, rem_wire!, rem_wires!, substitute!, all_neighbors,
  neighbors, out_neighbors, in_neighbors, in_wires, out_wires,
  dom, codom, id, compose, otimes, munit, braid, permute, mcopy, delete,
  mmerge, create, to_wiring_diagram

import Base: permute
using AutoHashEquals
using LightGraphs
import LightGraphs: all_neighbors, neighbors, out_neighbors, in_neighbors

using ...GAT, ...Syntax
import ...Doctrine: CategoryExpr, ObExpr, HomExpr, SymmetricMonoidalCategory,
  dom, codom, id, compose, otimes, munit, braid, mcopy, delete, mmerge, create
using ..Networks
import ..Networks: graph

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
  if wire.value != nothing
    print(io, wire.value)
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

""" Wiring diagram: morphism in the category of wiring diagrams.

The wiring diagram is implemented using the following internal data structures.
A LightGraphs `DiGraph` stores the "skeleton" of the diagram: a simple directed
graph with the boxes as vertices and with an edge between two vertices iff there
is at least one wire between the corresponding boxes. There are two special
vertices, accessible via `input_id` and `output_id`, representing the input and
output ports, respectively.

The `DiGraph` is wrapped inside a `DiNetwork` (borrowed from Networks.jl) to
attach properties to the vertices and edges. (At the time of this writing, the
Julia community has no standard graph data structure supporting aribtrary
graph/vertex/edge properties ala NetworkX in Python.) For each edge, an edge
property is used to store a list of wires between the source and target boxes.
"""
mutable struct WiringDiagram <: AbstractBox
  network::DiNetwork{Nullable{<:AbstractBox},Vector{WireEdgeData},Void}
  input_ports::Vector
  output_ports::Vector
  input_id::Int
  output_id::Int
  
  function WiringDiagram(input_ports::Vector, output_ports::Vector)
    network = DiNetwork(Nullable{<:AbstractBox}, Vector{WireEdgeData})
    diagram = new(network, input_ports, output_ports, 0, 0)
    diagram.input_id = add_vertex!(network, Nullable{AbstractBox}())
    diagram.output_id = add_vertex!(network, Nullable{AbstractBox}())
    return diagram
  end
end

function WiringDiagram(inputs::Ports, outputs::Ports)
  WiringDiagram(inputs.ports, outputs.ports)
end
WiringDiagram() = WiringDiagram([], [])

input_id(diagram::WiringDiagram) = diagram.input_id
output_id(diagram::WiringDiagram) = diagram.output_id

""" Check equality of wiring diagrams.

Warning: This method checks exact equality of the underlying graph
representation, not mathematical equality which involves graph isomorphism.
"""
function Base.:(==)(d1::WiringDiagram, d2::WiringDiagram)
  (input_ports(d1) == input_ports(d2) && output_ports(d1) == output_ports(d2) &&
   input_id(d1) == input_id(d2) && output_id(d1) == output_id(d2) &&
   graph(d1) == graph(d2) &&
   boxes(d1) == boxes(d2) && sort!(wires(d1)) == sort!(wires(d2)))
end

# Low-level graph interface
###########################

# Basic accessors.

box(f::WiringDiagram, v::Int) = get(getprop(f.network, v))
boxes(f::WiringDiagram) = AbstractBox[ box(f,v) for v in box_ids(f) ]
nboxes(f::WiringDiagram) = nv(graph(f)) - 2

function box_ids(f::WiringDiagram)
  skip = (input_id(f), output_id(f))
  Int[ v for v in 1:nv(graph(f)) if !(v in skip) ]
end

function wires(f::WiringDiagram, edge::Edge)
  if hasprop(f.network, edge)
    Wire[ from_edge_data(data, edge) for data in getprop(f.network, edge) ]
  else
    Wire[]
  end
end
wires(f::WiringDiagram, src::Int, tgt::Int) = wires(f, Edge(src,tgt))
wires(f::WiringDiagram) = vcat((wires(f,e) for e in edges(graph(f)))...)
nwires(f::WiringDiagram) =
  sum(Int[ length(getprop(f.network,e)) for e in edges(graph(f)) ])

function has_wire(f::WiringDiagram, src::Int, tgt::Int)
  has_edge(graph(f), Edge(src, tgt))
end
function has_wire(f::WiringDiagram, wire::Wire)
  wire in wires(f, wire.source.box, wire.target.box)
end
has_wire(f, pair::Pair) = has_wire(f, Wire(pair))

function port_value(f::WiringDiagram, port::Port)
  if port.box == input_id(f)
    input_ports(f)[port.port]
  elseif port.box == output_id(f)
    output_ports(f)[port.port]
  else
    box = Wiring.box(f, port.box)
    ports = port.kind == InputPort ? input_ports(box) : output_ports(box)
    ports[port.port]
  end
end

# Graph mutation.

function add_box!(f::WiringDiagram, box::AbstractBox)
  add_vertex!(f.network, Nullable(box))
end

function add_boxes!(f::WiringDiagram, boxes)
  for box in boxes
    add_box!(f, box)
  end
end

function rem_box!(f::WiringDiagram, v::Int)
  @assert !(v in (input_id(f), output_id(f)))
  rem_vertex!(f.network, v)
end

function rem_boxes!(f::WiringDiagram, vs::Vector{Int})
  # Remove boxes in descending order of vertex ID to maintain ID stability.
  for v in sort(vs, rev=true)
    rem_box!(f, v)
  end
end

function add_wire!(f::WiringDiagram, wire::Wire)
  # Check compatibility of port types.
  validate_ports(port_value(f, wire.source), port_value(f, wire.target))
  
  # Add edge and edge properties.
  edge = Edge(wire.source.box, wire.target.box)
  if !has_edge(f.network.graph, edge)
    add_edge!(f.network, edge, WireEdgeData[])
  end
  push!(getprop(f.network, edge), to_edge_data(wire))
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
  wires = getprop(f.network, edge)
  deleteat!(wires, findlast(d -> d == edge_data, wires))
  if isempty(wires)
    rem_edge!(f.network, edge)
  end
end
rem_wire!(f::WiringDiagram, pair::Pair) = rem_wire!(f, Wire(pair))

function rem_wires!(f::WiringDiagram, src::Int, tgt::Int)
  rem_edge!(f.network, Edge(src, tgt))
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
graph(diagram::WiringDiagram) = diagram.network.graph

# Convenience methods delegated to LightGraphs.
all_neighbors(d::WiringDiagram, v::Int) = all_neighbors(graph(d), v)
neighbors(d::WiringDiagram, v::Int) = neighbors(graph(d), v)
out_neighbors(d::WiringDiagram, v::Int) = out_neighbors(graph(d), v)
in_neighbors(d::WiringDiagram, v::Int) = in_neighbors(graph(d), v)

""" Get all wires coming into or out of the box.
"""
function wires(d::WiringDiagram, v::Int)
  result = wires(d, v, v)
  for u in in_neighbors(d, v)
    if u != v
      append!(result, wires(d, u, v))
    end
  end
  for u in out_neighbors(d, v)
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
  for u in in_neighbors(d, v)
    append!(result, wires(d, u, v))
  end
  result
end

""" Get all wires coming into the port.
"""
function in_wires(d::WiringDiagram, port::Port)
  result = Wire[]
  for v in in_neighbors(d, port.box)
    for wire in wires(d, v, port.box)
      if wire.target == port
        push!(result, wire)
      end
    end
  end
  result
end

""" Get all wires coming out of the box.
"""
function out_wires(d::WiringDiagram, v::Int)
  result = Wire[]
  for u in out_neighbors(d, v)
    append!(result, wires(d, v, u))
  end
  result
end

""" Get all wires coming out of the port.
"""
function out_wires(d::WiringDiagram, port::Port)
  result = Wire[]
  for v in out_neighbors(d, port.box)
    for wire in wires(d, port.box, v)
      if wire.source == port
        push!(result, wire)
      end
    end
  end
  result
end

# Diagram substitution.

""" Substitute a wiring diagram for a vertex.

This operation is the operadic composition of wiring diagrams.
"""
function substitute!(d::WiringDiagram, v::Int, sub::WiringDiagram)
  substitute_impl!(d, v, sub)
  rem_box!(d, v)
  return d
end
function substitute!(d::WiringDiagram, v::Int)
  substitute!(d, v, box(d,v))
end

""" Simultaneous substitution of wiring diagrams for vertices.
"""
function substitute!(d::WiringDiagram, vs::Vector{Int}, subs::Vector{WiringDiagram})
  for (v,sub) in zip(vs, subs)
    substitute_impl!(d, v, sub)
  end
  rem_boxes!(d, vs)
  return d
end
function substitute!(d::WiringDiagram, vs::Vector{Int})
  substitute!(d, vs, WiringDiagram[ box(d,v) for v in vs ])
end

function substitute_impl!(d::WiringDiagram, v::Int, sub::WiringDiagram)
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
      for in_wire in in_wires(d, Port(v,InputPort,wire.source.port))
        for out_wire in out_wires(d, Port(v,OutputPort,wire.target.port))
          add_wire!(d, Wire(in_wire.source, out_wire.target))
        end
      end
    # Special case: wire from input port to internal box.
    elseif wire.source.box == input_id(sub)
      for in_wire in in_wires(d, Port(v,InputPort,wire.source.port))
        add_wire!(d, Wire(in_wire.source, set_box(wire.target, tgt)))
      end  
    # Special case: wire from internal box to output port.
    elseif wire.target.box == output_id(sub)
      for out_wire in out_wires(d, Port(v,OutputPort,wire.target.port))
        add_wire!(d, Wire(set_box(wire.source, src), out_wire.target))
      end
    # Default case: wire between two internal boxes.
    else
      add_wire!(d, Wire(set_box(wire.source, src), set_box(wire.target, tgt)))
    end
  end
  return d
end

# High-level categorical interface
##################################

""" Create box for a morphism generator expression.
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

""" Create wiring diagram with a single box containing a morphism expression.
"""
function WiringDiagram(f::HomExpr)
  d = WiringDiagram(dom(f), codom(f))
  fv = add_box!(d, Box(f))
  add_wires!(d, ((input_id(d),i) => (fv,i) for i in eachindex(dom(d))))
  add_wires!(d, ((fv,i) => (output_id(d),i) for i in eachindex(codom(d))))
  return d
end

""" Wiring diagram as *symmetric monoidal category*.

Wiring diagrams also have *diagonals* and *codiagonals* (see extra methods),
but we don't have doctrines for those yet.
"""
@instance SymmetricMonoidalCategory(Ports, WiringDiagram) begin
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

function mcopy(A::Ports, n::Int=2)::WiringDiagram
  f = WiringDiagram(A, otimes([A for j in 1:n]))
  m = length(A)
  for j in 1:n
    add_wires!(f, ((input_id(f),i) => (output_id(f),i+m*(j-1)) for i in 1:m))
  end
  return f
end

function mmerge(A::Ports, n::Int=2)::WiringDiagram
  f = WiringDiagram(otimes([A for j in 1:n]), A)
  m = length(A)
  for j in 1:n
    add_wires!(f, ((input_id(f),i+m*(j-1)) => (output_id(f),i) for i in 1:m))
  end
  return f
end

delete(A::Ports) = WiringDiagram(A, munit(Ports))
create(A::Ports) = WiringDiagram(munit(Ports), A)

""" Convert a syntactic expression into a wiring diagram.

The morphism expression should belong to the doctrine of symmetric monoidal
categories, possibly with diagonals and codiagonals. Thus, the doctrines of
cartesian, cocartesian, and biproduct categories are supported.
"""
function to_wiring_diagram(expr::CategoryExpr)
  functor((Ports, WiringDiagram), expr;
    terms = Dict(
      :Ob => (expr) -> Ports([first(expr)]),
      :Hom => (expr) -> WiringDiagram(expr),
    )
  )
end

function collect_values(ob::ObExpr)::Vector
  exprs = collect(ob)
  @assert all(head(expr) == :generator for expr in exprs)
  return map(first, exprs)
end

end
