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
export Box, HomBox, WiringDiagram, Wire, WireTypes, Connector, ConnectorKind,
  Input, Output, inputs, outputs, input_id, output_id,
  nboxes, nwires, box, wires, has_wire,
  add_box!, add_boxes!, add_wire!, rem_box!, rem_wire!, rem_wires!,
  graph, all_neighbors, neighbors, out_neighbors, in_neighbors

using AutoHashEquals
using LightGraphs, Networks
import LightGraphs: all_neighbors, neighbors, out_neighbors, in_neighbors
using ...Syntax
import ...Doctrine: ObExpr, HomExpr

# Data types
############

""" Base type for any box (node) in a wiring diagram.

This type represents an arbitrary black box with (possibly empty) lists of
inputs and outputs.
"""
abstract Box

""" A box representing a morphism expression, often a generator.

These boxes have no internal structure.
"""
@auto_hash_equals immutable HomBox <: Box
  expr::HomExpr
end
inputs(box::HomBox) = collect(dom(box.expr))
outputs(box::HomBox) = collect(codom(box.expr))

@enum ConnectorKind Input Output
@auto_hash_equals immutable Connector
  box::Int
  kind::ConnectorKind
  port::Int
end

@auto_hash_equals immutable Wire
  source::Connector
  target::Connector
  Wire(src::Connector, tgt::Connector) = new(src, tgt)
  Wire(src::Tuple, tgt::Tuple) = new(Connector(src...), Connector(tgt...))
  Wire(pair::Pair) = Wire(first(pair), last(pair))
end

""" Object in the category of wiring diagrams.
"""
@auto_hash_equals immutable WireTypes
  types::Vector
end

""" Morphism in the category of wiring diagrams.

TODO: Document internal representation.
"""
type WiringDiagram <: Box
  network::DiNetwork{Box,Vector{Wire},Void}
  inputs::Vector
  outputs::Vector
  input_id::Int
  output_id::Int
  
  function WiringDiagram(inputs::Vector, outputs::Vector)
    network = DiNetwork(DiGraph(), Dict{Int,Box}(),
                        Dict{Edge,Vector{Wire}}(), Void())
    diagram = new(network, inputs, outputs, 0, 0)
    diagram.input_id = add_box!(diagram, diagram)
    diagram.output_id = add_box!(diagram, diagram)
    return diagram
  end
  function WiringDiagram(inputs::ObExpr, outputs::ObExpr)
    WiringDiagram(collect(inputs), collect(outputs))
  end
end
inputs(diagram::WiringDiagram) = diagram.inputs
outputs(diagram::WiringDiagram) = diagram.outputs
input_id(diagram::WiringDiagram) = diagram.input_id
output_id(diagram::WiringDiagram) = diagram.output_id

# Low-level graph interface
###########################

# Basic accessors.

box(f::WiringDiagram, v::Int) = f.network.vprops[v]
wires(f::WiringDiagram, edge::Edge) = get(f.network.eprops, edge, Wire[])
wires(f::WiringDiagram, src::Int, tgt::Int) = wires(f, Edge(src,tgt))
nboxes(f::WiringDiagram) = nv(f.network.graph) - 2
nwires(f::WiringDiagram) = sum(Int[length(w) for w in values(f.network.eprops)])

function has_wire(f::WiringDiagram, src::Int, tgt::Int)
  has_edge(f.network.graph, Edge(src, tgt))
end

# Graph mutation.

function add_box!(f::WiringDiagram, box::Box)
  add_vertex!(f.network, box)
end
add_box!(f::WiringDiagram, expr::HomExpr) = add_box!(f, HomBox(expr))

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
    add_edge!(f.network, edge, Wire[])
  end
  push!(f.network.eprops[edge], wire)
end
add_wire!(f::WiringDiagram, pair::Pair) = add_wire!(f, Wire(pair))

function rem_wire!(f::WiringDiagram, wire::Wire)
  edge = Edge(wire.source.box, wire.target.box)
  wires = f.eprops[edge]
  deleteat!(wires, findfirst(wires, wire))
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

# High-level categorical interface
##################################

# @instance SymmetricMonoidalCategory(WireTypes, WiringDiagram) begin
#   dom(f::WiringDiagram) = WireTypes(f.inputs)
#   codom(f::WiringDiagram) = WireTypes(f.outputs)
# end

end
