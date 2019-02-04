""" Data structure for connecting one layer to another by wires.

This module defines a generic data structure to represent a wiring between one
layer of input ports to another layer of output ports. A wiring layer forms
bipartite graph with independent edge sets the input ports and the output ports.

Unlike wiring diagrams, wiring layers are an auxillary data structure. They are
not terribly interesting in their own right, but they are useful intermediate
representation in some circumstances. For example, a morphism expression
comprised of generators, compositions, products, and wiring layers is
intermediate between a pure GAT expression (which has no wiring layers, but may
have identities, braidings, copies, etc.) and a wiring diagram, which is purely
graphical.
"""
module WiringLayers
export WiringLayer, Layer, input_ports, output_ports, nwires, wires, has_wire,
  add_wire!, add_wires!, rem_wire!, rem_wires!, to_wiring_diagram,
  dom, codom, id, compose, otimes, munit, braid, mcopy, delete, mmerge, create

using AutoHashEquals

using ...GAT, ...Syntax
import ...Doctrines: MonoidalCategoryWithBidiagonals,
  dom, codom, id, compose, otimes, munit, braid, mcopy, delete, mmerge, create
using ..WiringDiagramCore
import ..WiringDiagramCore: input_ports, output_ports, nwires, wires, has_wire,
  add_wire!, add_wires!, rem_wire!, rem_wires!, to_wiring_diagram

# Data types
############

""" Connection by wires of one layer to another.

Morphism in the category of wiring layers.
"""
@auto_hash_equals struct WiringLayer{T}
  wires::Dict{Pair{Int,Int},Int} # Multiset of wires
  input_ports::Vector{T}
  output_ports::Vector{T}

  function WiringLayer(inputs::Vector{T}, outputs::Vector{T}) where T
    new{T}(Dict{Pair{Int,Int},Int}(), inputs, outputs)
  end
end

""" A layer, constituted by a list of ports.

Object in the category of wiring layers.
"""
@auto_hash_equals struct Layer{T}
  ports::Vector{T}
end

# Low-level graph interface
###########################

function WiringLayer(wires, inputs, outputs)
  f = WiringLayer(inputs, outputs)
  add_wires!(f, wires)
  f
end

input_ports(f::WiringLayer) = f.input_ports
output_ports(f::WiringLayer) = f.output_ports

nwires(f::WiringLayer) = sum(values(f.wires))
nwires(f::WiringLayer, wire) = get(f.wires, wire, 0)
has_wire(f::WiringLayer, wire) = nwires(f, wire) > 0
wires(f::WiringLayer) = vcat((repeat([wire],n) for (wire,n) in f.wires)...)

function add_wire!(f::WiringLayer, wire)
  src, tgt = wire
  if !(1 <= src <= length(f.input_ports))
    throw(BoundsError("layer inputs $(f.input_ports)", src))
  end
  if !(1 <= tgt <= length(f.output_ports))
    throw(BoundsError("layer outputs $(f.output_ports)", tgt))
  end
  if haskey(f.wires, wire)
    f.wires[wire] += 1
  else
    f.wires[wire] = 1
  end
end

function add_wires!(f::WiringLayer, wires)
  for wire in wires
    add_wire!(f, wire)
  end
end

function rem_wire!(f::WiringLayer, wire)
  if f.wires[wire] <= 1
    delete!(f.wires, wire)
  else
    f.wires[wire] -= 1
  end
end

rem_wires!(f::WiringLayer, wire) = delete!(f.wires, wire)

function to_wiring_diagram(f::WiringLayer)
  diagram = WiringDiagram(input_ports(f), output_ports(f))
  add_wires!(diagram, ((input_id(diagram), src) => (output_id(diagram), tgt)
                       for (src, tgt) in sort!(wires(f))))
  diagram
end

# High-level categorical interface
##################################

# """ Wiring layers as *monoidal category with diagonals and codiagonals*.
# """
# @instance MonoidalCategoryWithBidiagonals(Layer, WiringLayer) begin
#   dom(f::WiringLayer) = Layer(f.inputs)
#   codom(f::WiringLayer) = Layer(f.outputs)
# end

end
