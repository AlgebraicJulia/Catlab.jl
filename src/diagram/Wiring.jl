""" Wiring diagram for monoidal categories.

A wiring diagram a graphical representation of a morphism in a monoidal
category. It is intermediate between a morphism (as an mathematical entity) and
an expression in the textual syntax: a single morphism may be represented by
many wiring diagrams, and a single wiring diagram may be represented by many
syntactic expressions.

The wiring diagrams in this module are "abstract" in the sense that they cannot
be directly rendered as raster or vector graphics. However, they form a useful
intermediate representation that can be straightforwardly translated into
Graphviz or other declarative diagram languages.
"""
module Wiring
export Box, HomBox, WiringDiagram, Wire, WireTypes, Port, PortKind,
  Input, Output, inputs, outputs, input_id, output_id,
  boxes, box_ids, nboxes, nwires, box, wires, has_wire, graph,
  add_box!, add_boxes!, add_wire!, add_wires!, rem_box!, rem_wire!, rem_wires!,
  all_neighbors, neighbors, out_neighbors, in_neighbors, in_wires, out_wires,
  substitute!

using AutoHashEquals
import DataStructures: OrderedSet
using LightGraphs
import LightGraphs: all_neighbors, neighbors, out_neighbors, in_neighbors

using ...GAT, ...Syntax
import ...Doctrine: ObExpr, HomExpr, SymmetricMonoidalCategory, 
  dom, codom, id, compose, otimes, munit, braid
using ..Networks
import ..Networks: graph

# Data types
############

""" Kind of port: input or output.
"""
@enum PortKind Input Output

""" A port on a box to which wires can be connected.
"""
@auto_hash_equals immutable Port
  box::Int
  kind::PortKind
  port::Int
end
function set_box(conn::Port, box::Int)::Port
  Port(box, conn.kind, conn.port)
end

""" A wire connecting one port to another.
"""
@auto_hash_equals immutable Wire
  source::Port
  target::Port
  
  Wire(src::Port, tgt::Port) = new(src, tgt)
  Wire(src::Tuple{Int,PortKind,Int}, tgt::Tuple{Int,PortKind,Int}) =
    Wire(Port(src[1],src[2],src[3]), Port(tgt[1],tgt[2],tgt[3]))
  Wire(src::Tuple{Int,Int}, tgt::Tuple{Int,Int}) =
    Wire(Port(src[1],Output,src[2]), Port(tgt[1],Input,tgt[2]))
  Wire(pair::Pair) = Wire(first(pair), last(pair))
end

@auto_hash_equals immutable PortEdgeData
  kind::PortKind
  port::Int
end
to_edge_data(conn::Port) = PortEdgeData(conn.kind, conn.port)
from_edge_data(conn::PortEdgeData, v::Int) = Port(v, conn.kind, conn.port)

@auto_hash_equals immutable WireEdgeData
  source::PortEdgeData
  target::PortEdgeData
end
function to_edge_data(wire::Wire)
  WireEdgeData(to_edge_data(wire.source), to_edge_data(wire.target))
end
function from_edge_data(wire::WireEdgeData, edge::Edge)
  Wire(from_edge_data(wire.source, first(edge)),
       from_edge_data(wire.target, last(edge)))
end

""" Object in the category of wiring diagrams.
"""
@auto_hash_equals immutable WireTypes
  types::Vector
end
Base.eachindex(A::WireTypes) = eachindex(A.types)
Base.length(A::WireTypes) = length(A.types)

""" Base type for any box (node) in a wiring diagram.

This type represents an arbitrary black box with (possibly empty) lists of
inputs and outputs.
"""
abstract Box

""" Morphism in the category of wiring diagrams.

TODO: Document internal representation.
"""
type WiringDiagram <: Box
  network::DiNetwork{Box,OrderedSet{WireEdgeData},Void}
  inputs::Vector
  outputs::Vector
  input_id::Int
  output_id::Int
  
  function WiringDiagram(inputs::Vector, outputs::Vector)
    network = DiNetwork(Box, OrderedSet{WireEdgeData})
    diagram = new(network, inputs, outputs, 0, 0)
    diagram.input_id = add_box!(diagram, diagram)
    diagram.output_id = add_box!(diagram, diagram)
    return diagram
  end
  function WiringDiagram(inputs::WireTypes, outputs::WireTypes)
    WiringDiagram(inputs.types, outputs.types)
  end
end
inputs(diagram::WiringDiagram) = diagram.inputs
outputs(diagram::WiringDiagram) = diagram.outputs
input_id(diagram::WiringDiagram) = diagram.input_id
output_id(diagram::WiringDiagram) = diagram.output_id

""" Check equality of wiring diagrams.

Warning: This method checks exact equality of the underlying graph
representation, not mathematical equality which involves graph isomorphism.
"""
function Base.:(==)(d1::WiringDiagram, d2::WiringDiagram)
  (inputs(d1) == inputs(d2) && outputs(d1) == outputs(d2) &&
   input_id(d1) == input_id(d2) && output_id(d1) == output_id(d2) &&
   graph(d1) == graph(d2) &&
   boxes(d1) == boxes(d2) &&
   all(getprop(d1.network,e) == getprop(d2.network,e) for e in edges(graph(d1))))
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

# Graph mutation.

function add_box!(f::WiringDiagram, box::Box)
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
  # TODO: Check for compatible inputs/outputs.
  edge = Edge(wire.source.box, wire.target.box)
  if !has_edge(f.network.graph, edge)
    add_edge!(f.network, edge, OrderedSet{WireEdgeData}())
  end
  push!(getprop(f.network, edge), to_edge_data(wire))
end
add_wire!(f::WiringDiagram, pair::Pair) = add_wire!(f, Wire(pair))

function add_wires!(f::WiringDiagram, wires)
  for wire in wires
    add_wire!(f, wire)
  end
end

# TODO: Test function!
function rem_wire!(f::WiringDiagram, wire::Wire)
  edge = Edge(wire.source.box, wire.target.box)
  wires = getprop(f.network, edge)
  deleteat!(wires, findfirst(wires, to_wire_data(wire)))
  if isempty(wires)
    rem_edge!(f.network, edge)
  end
end

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

""" Get all wires coming into the connector.
"""
function in_wires(d::WiringDiagram, conn::Port)
  result = Wire[]
  for v in in_neighbors(d, conn.box)
    for wire in wires(d, v, conn.box)
      if wire.target == conn
        push!(result, wire)
      end
    end
  end
  result
end

""" Get all wires coming out of the connector.
"""
function out_wires(d::WiringDiagram, conn::Port)
  result = Wire[]
  for v in out_neighbors(d, conn.box)
    for wire in wires(d, conn.box, v)
      if wire.source == conn
        push!(result, wire)
      end
    end
  end
  result
end

# Diagram substitution.

""" Substitute a vertex with a wiring diagram.

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

""" Simultaneous substitution of vertices with wiring diagrams.
"""
function substitute!(d::WiringDiagram, vs::Vector{Int}, subs::Vector{WiringDiagram})
  for (v,sub) in zip(vs, subs)
    substitute_impl!(d, v, sub)
  end
  for v in reverse(vs)
    rem_box!(d,v)
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

""" A box representing a morphism expression, often a generator.

These boxes have no internal structure.
"""
@auto_hash_equals immutable HomBox <: Box
  expr::HomExpr
end
inputs(box::HomBox) = collect(dom(box.expr))
outputs(box::HomBox) = collect(codom(box.expr))

""" Create empty wiring diagram with given domain and codomain objects.
"""
function WiringDiagram(inputs::ObExpr, outputs::ObExpr)
  WiringDiagram(collect(inputs), collect(outputs))
end

""" Create wiring diagram with a single morphism box.
"""
function WiringDiagram(f::HomExpr)
  d = WiringDiagram(dom(f), codom(f))
  fv = add_box!(d, f)
  add_wires!(d, ((input_id(d),i) => (fv,i) for i in eachindex(dom(d))))
  add_wires!(d, ((fv,i) => (output_id(d),i) for i in eachindex(codom(d))))
  return d
end

add_box!(f::WiringDiagram, expr::HomExpr) = add_box!(f, HomBox(expr))

@instance SymmetricMonoidalCategory(WireTypes, WiringDiagram) begin
  dom(f::WiringDiagram) = WireTypes(f.inputs)
  codom(f::WiringDiagram) = WireTypes(f.outputs)
  
  function id(A::WireTypes)
    f = WiringDiagram(A, A)
    add_wires!(f, ((input_id(f),i) => (output_id(f),i) for i in eachindex(A)))
    return f
  end
  
  function compose(f::WiringDiagram, g::WiringDiagram)
    h = WiringDiagram(dom(f), codom(g))
    fv = add_box!(h, f)
    gv = add_box!(h, g)
    add_wires!(h, ((input_id(h),i) => (fv,i) for i in eachindex(dom(f))))
    add_wires!(h, ((fv,i) => (gv,i) for i in eachindex(codom(f))))
    add_wires!(h, ((gv,i) => (output_id(h),i) for i in eachindex(dom(g))))
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

end
