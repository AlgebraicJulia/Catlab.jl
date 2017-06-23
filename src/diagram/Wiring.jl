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
export WiringDiagram, Node, ExprNode, Wire, WireTypes,
  Connector, ConnectorKind, Input, Output,
  add_node!, add_wire!, rem_node!, rem_wire!, has_node, has_wire

using AutoHashEquals
using LightGraphs, Networks
import LightGraphs: Edge
using ...Syntax
import ...Doctrine: ObExpr, HomExpr

# Data types
############

""" Base type for any node (vertex) in a wiring diagram.
"""
abstract Node

@enum ConnectorKind Input Output
immutable Connector
  node::Node
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

""" Node representing a morphism expression, often a generator.

These nodes have no internal structure.
"""
immutable ExprNode <: Node
  expr::HomExpr
end
dom(node::ExprNode) = WireTypes(dom(node.expr))
codom(node::ExprNode) = WireTypes(codom(node.expr))

""" Morphism in the category of wiring diagrams.
"""
type WiringDiagram <: Node
  inputs::WireTypes
  outputs::WireTypes
  network::DiNetwork{Node,Vector{Wire},Void}
  vertices::Dict{Node,Int}
  
  function WiringDiagram(inputs::WireTypes, outputs::WireTypes)
    network = DiNetwork(DiGraph(), Dict{Int,Node}(),
                        Dict{Edge,Vector{Wire}}(), Void())
    diagram = new(inputs, outputs, network, Dict{Node,Int}())
    add_node!(diagram, diagram)
    return diagram
  end
  function WiringDiagram(inputs::ObExpr, outputs::ObExpr)
    WiringDiagram(WireTypes(inputs), WireTypes(outputs))
  end
end

# Low-level graph interface
###########################

function add_node!(f::WiringDiagram, node::Node)
  v = add_vertex!(f.network, node)
  f.vertices[node] = v
  return node
end
function add_node!(f::WiringDiagram, expr::HomExpr)
  add_node!(f, ExprNode(expr))
end

function add_wire!(f::WiringDiagram, wire::Wire)
  edge = Edge(f, wire)
  if !has_edge(f.graph, edge)
    add_edge!(f, edge, Wire[])
  end
  push!(f.eprops[edge], wire)
end

function rem_node!(f::WiringDiagram, node::Node)
  rem_vertex!(f.network, f.vertices[node])
  delete!(f.vertices, node)
end

function rem_wire!(f::WiringDiagram, wire::Wire)
  edge = Edge(f, wire)
  wires = f.eprops[edge]
  deleteat!(wires, findfirst(wires, wire))
  if isempty(wires)
    rem_edge!(f.network, edge)
  end
end

function has_node(f::WiringDiagram, node::Node)
  haskey(f.vertices, node)
end

function has_wire(f::WiringDiagram, src::Node, tgt::Node)
  has_edge(f.network.graph, Edge(f, src, tgt))
end

Edge(f::WiringDiagram, wire::Wire) = Edge(f, wire.source, wire.target)
Edge(f::WiringDiagram, src::Node, tgt::Node) = 
  Edge(f.vertices[src], f.vertices[wire.target])

# High-level categorical interface
##################################

# @instance SymmetricMonoidalCategory(WireTypes, WiringDiagram) begin
#   dom(g::WiringDiagram) = f.inputs
#   codom(g::WiringDiagram) = f.outputs
# end

end
