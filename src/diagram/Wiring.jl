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
  Input, Output, nboxes, box, wires,
  add_box!, add_wire!, rem_box!, rem_wire!, has_wire

using AutoHashEquals
using LightGraphs, Networks
using ...Syntax
import ...Doctrine: ObExpr, HomExpr

# Data types
############

""" Base type for any box (node) in a wiring diagram.
"""
abstract Box

""" A box representing a morphism expression, often a generator.

These boxes have no internal structure.
"""
@auto_hash_equals immutable HomBox <: Box
  expr::HomExpr
end
inputs(box::HomBox) = WireTypes(dom(box.expr))
outputs(box::HomBox) = WireTypes(codom(box.expr))

@enum ConnectorKind Input Output
immutable Connector
  box::Int
  kind::ConnectorKind
  port::Int
end

immutable Wire
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
  WireTypes(types::Vector) = new(types)
  WireTypes(expr::ObExpr) = new(collect(expr))
end

""" Morphism in the category of wiring diagrams.
"""
type WiringDiagram <: Box
  inputs::WireTypes
  outputs::WireTypes
  network::DiNetwork{Box,Vector{Wire},Void}
  
  function WiringDiagram(inputs::WireTypes, outputs::WireTypes)
    network = DiNetwork(DiGraph(), Dict{Int,Box}(),
                        Dict{Edge,Vector{Wire}}(), Void())
    diagram = new(inputs, outputs, network)
    add_box!(diagram, diagram)
    return diagram
  end
  function WiringDiagram(inputs::ObExpr, outputs::ObExpr)
    WiringDiagram(WireTypes(inputs), WireTypes(outputs))
  end
end
inputs(diagram::WiringDiagram) = diagram.inputs
outputs(diagram::WiringDiagram) = diagram.outputs

# Low-level graph interface
###########################

nboxes(f::WiringDiagram) = nv(f.network.graph)
box(f::WiringDiagram, v::Int) = f.network.vprops[v]
wires(f::WiringDiagram, edge::Edge) = f.network.eprops[edge]
wires(f::WiringDiagram, src::Int, tgt::Int) = wires(f, Edge(src,tgt))

function add_box!(f::WiringDiagram, box::Box)
  add_vertex!(f.network, box)
end
add_box!(f::WiringDiagram, expr::HomExpr) = add_box!(f, HomBox(expr))

function add_wire!(f::WiringDiagram, wire::Wire)
  # TODO: Check for compatible inputs/outputs.
  edge = Edge(wire.source.box, wire.target.box)
  if !has_edge(f.network.graph, edge)
    add_edge!(f.network, edge, Wire[])
  end
  push!(f.network.eprops[edge], wire)
end

function rem_box!(f::WiringDiagram, v::Int)
  rem_vertex!(f.network, v)
end

function rem_wire!(f::WiringDiagram, wire::Wire)
  edge = Edge(wire.source.box, wire.target.box)
  wires = f.eprops[edge]
  deleteat!(wires, findfirst(wires, wire))
  if isempty(wires)
    rem_edge!(f.network, edge)
  end
end

function has_wire(f::WiringDiagram, src::Int, tgt::Int)
  has_edge(f.network.graph, Edge(src, tgt))
end

# High-level categorical interface
##################################

# @instance SymmetricMonoidalCategory(WireTypes, WiringDiagram) begin
#   dom(f::WiringDiagram) = f.inputs
#   codom(f::WiringDiagram) = f.outputs
# end

end
