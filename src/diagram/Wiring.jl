""" Wiring diagram for monoidal categories.

A wiring diagram a graphical representation of a morphism in a monoidal
category. It is intermediate between a morphism (as an mathematical entity) and
an expression in the textual syntax: a single morphism may be represented by
many wiring diagrams, and a single wiring diagram may be represented by many
syntactic expressions.

The wiring diagrams in this module are "abstract" in the sense that they cannot
be directly rendered as raster or vector graphics. However, they form a useful
intermediate representation that can be straightforwardly serialized into
GraphML or translated into Graphviz or other declarative diagram languages.
"""
module Wiring
export AbstractBox, Box, WiringDiagram, Wire, WireTypes, WireTypeError, 
  Port, PortKind, Input, Output, input_types, output_types, input_id, output_id,
  boxes, box_ids, nboxes, nwires, box, wires, has_wire, wire_type, graph,
  add_box!, add_boxes!, add_wire!, add_wires!, validate_wire_types,
  rem_box!, rem_wire!, rem_wires!,
  all_neighbors, neighbors, out_neighbors, in_neighbors, in_wires, out_wires,
  substitute!, to_wiring_diagram

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
@enum PortKind Input Output

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
  Wire(value, Port(src[1],Output,src[2]), Port(tgt[1],Input,tgt[2]))
Wire(value, pair::Pair) = Wire(value, first(pair), last(pair))

Wire(src::Port, tgt::Port) = Wire(nothing, src, tgt)
Wire(src::Tuple, tgt::Tuple) = Wire(nothing, src, tgt)
Wire(pair::Pair) = Wire(nothing, first(pair), last(pair))

function Base.show(io::IO, wire::Wire)
  skip_kind = wire.source.kind == Output && wire.target.kind == Input
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

""" Object in the category of wiring diagrams.
"""
@auto_hash_equals struct WireTypes{WireType}
  types::Vector{WireType}
end
Base.eachindex(A::WireTypes) = eachindex(A.types)
Base.length(A::WireTypes) = length(A.types)

""" Exception thrown when types of source and target ports are not equal.
"""
struct WireTypeError <: Exception
  source_type::Any
  target_type::Any
end
function Base.showerror(io::IO, exc::WireTypeError)
  print(io, `Wire types $(exc.source_type) and $(exc.target_type) are not equal`)
end

""" Base type for any box (node) in a wiring diagram.

This type represents an arbitrary black box with inputs and outputs.
"""
abstract type AbstractBox end

input_types(box::AbstractBox)::Vector = box.input_types
output_types(box::AbstractBox)::Vector = box.output_types

""" An atomic box in a wiring diagram.

These boxes have no internal structure.
"""
@auto_hash_equals struct Box{Value} <: AbstractBox
  value::Value
  input_types::Vector
  output_types::Vector
end

""" Morphism in the category of wiring diagrams.

A wiring diagram is represented using the following data structures. A
LightGraphs `DiGraph` stores the "skeleton" of the diagram: a simple directed
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
  network::DiNetwork{AbstractBox,Vector{WireEdgeData},Void}
  input_types::Vector
  output_types::Vector
  input_id::Int
  output_id::Int
  
  function WiringDiagram(input_types::Vector, output_types::Vector)
    network = DiNetwork(AbstractBox, Vector{WireEdgeData})
    diagram = new(network, input_types, output_types, 0, 0)
    diagram.input_id = add_box!(diagram, diagram)
    diagram.output_id = add_box!(diagram, diagram)
    return diagram
  end
  function WiringDiagram(inputs::WireTypes, outputs::WireTypes)
    WiringDiagram(inputs.types, outputs.types)
  end
end
input_id(diagram::WiringDiagram) = diagram.input_id
output_id(diagram::WiringDiagram) = diagram.output_id

""" Check equality of wiring diagrams.

Warning: This method checks exact equality of the underlying graph
representation, not mathematical equality which involves graph isomorphism.
"""
function Base.:(==)(d1::WiringDiagram, d2::WiringDiagram)
  (input_types(d1) == input_types(d2) && output_types(d1) == output_types(d2) &&
   input_id(d1) == input_id(d2) && output_id(d1) == output_id(d2) &&
   graph(d1) == graph(d2) &&
   boxes(d1) == boxes(d2) && sort!(wires(d1)) == sort!(wires(d2)))
end

# Low-level graph interface
###########################

# Basic accessors.

box(f::WiringDiagram, v::Int) = getprop(f.network, v)
boxes(f::WiringDiagram) = [ box(f,v) for v in box_ids(f) ]
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

function wire_type(f::WiringDiagram, port::Port)
  if port.box == input_id(f)
    input_types(f)[port.port]
  elseif port.box == output_id(f)
    output_types(f)[port.port]
  else
    box = Wiring.box(f, port.box)
    types = port.kind == Input ? input_types(box) : output_types(box)
    types[port.port]
  end
end
function wire_type(f::WiringDiagram, wire::Wire)
  @assert has_wire(f, wire)
  wire_type(f, wire.source) # == wire_type(f, wire.target)
end
wire_type(f, pair::Pair) = wire_type(f, Wire(pair))

# Graph mutation.

function add_box!(f::WiringDiagram, box::AbstractBox)
  add_vertex!(f.network, box)
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

function add_wire!(f::WiringDiagram, wire::Wire)
  # Check for compatible types.
  source_type = wire_type(f, wire.source)
  target_type = wire_type(f, wire.target)
  validate_wire_types(source_type, target_type)
  
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

function validate_wire_types(source_type, target_type)
  if source_type != target_type
    throw(WireTypeError(source_type, target_type))
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
  for v in reverse(vs)
    rem_box!(d, v)
  end
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
      for in_wire in in_wires(d, Port(v,Input,wire.source.port))
        for out_wire in out_wires(d, Port(v,Output,wire.target.port))
          add_wire!(d, Wire(in_wire.source, out_wire.target))
        end
      end
    # Special case: wire from input port to internal box.
    elseif wire.source.box == input_id(sub)
      for in_wire in in_wires(d, Port(v,Input,wire.source.port))
        add_wire!(d, Wire(in_wire.source, set_box(wire.target, tgt)))
      end  
    # Special case: wire from internal box to output port.
    elseif wire.target.box == output_id(sub)
      for out_wire in out_wires(d, Port(v,Output,wire.target.port))
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
@instance SymmetricMonoidalCategory(WireTypes, WiringDiagram) begin
  dom(f::WiringDiagram) = WireTypes(f.input_types)
  codom(f::WiringDiagram) = WireTypes(f.output_types)
  
  function id(A::WireTypes)
    f = WiringDiagram(A, A)
    add_wires!(f, ((input_id(f),i) => (output_id(f),i) for i in eachindex(A)))
    return f
  end
  
  function compose(f::WiringDiagram, g::WiringDiagram)
    if codom(f) != dom(g)
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
  
  otimes(A::WireTypes, B::WireTypes) = WireTypes([A.types; B.types])
  munit(::Type{WireTypes}) = WireTypes([])
  
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
  
  function braid(A::WireTypes, B::WireTypes)
    h = WiringDiagram(otimes(A,B), otimes(B,A))
    m, n = length(A), length(B)
    add_wires!(h, ((input_id(h),i) => (output_id(h),i+n) for i in 1:m))
    add_wires!(h, ((input_id(h),i+m) => (output_id(h),i) for i in 1:n))
    return h
  end
end

function mcopy(A::WireTypes, n::Int=2)::WiringDiagram
  f = WiringDiagram(A, otimes([A for j in 1:n]))
  m = length(A)
  for j in 1:n
    add_wires!(f, ((input_id(f),i) => (output_id(f),i+m*(j-1)) for i in 1:m))
  end
  return f
end

function mmerge(A::WireTypes, n::Int=2)::WiringDiagram
  f = WiringDiagram(otimes([A for j in 1:n]), A)
  m = length(A)
  for j in 1:n
    add_wires!(f, ((input_id(f),i+m*(j-1)) => (output_id(f),i) for i in 1:m))
  end
  return f
end

delete(A::WireTypes) = WiringDiagram(A, munit(WireTypes))
create(A::WireTypes) = WiringDiagram(munit(WireTypes), A)

""" Convert a syntactic expression into a wiring diagram.

The morphism expression should belong to the doctrine of symmetric monoidal
categories, possibly with diagonals and codiagonals. Thus, the doctrines of
cartesian, cocartesian, and biproduct categories are supported.
"""
function to_wiring_diagram(expr::CategoryExpr)
  functor((WireTypes, WiringDiagram), expr;
    terms = Dict(
      :Ob => (expr) -> WireTypes([first(expr)]),
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
