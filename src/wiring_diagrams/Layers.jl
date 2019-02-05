""" Data structure for connecting one layer to another by wires.

This module defines a generic data structure to represent a wiring between one
layer of input ports and another layer of output ports. A wiring layer forms a
bipartite graph with independent edge sets the input ports and the output ports.

Unlike wiring diagrams, wiring layers are an auxillary data structure. They are
not terribly interesting in their own right, but they are a useful intermediate
representation in some circumstances. For example, a morphism expression
comprised of generators, compositions, products, and wiring layers is
intermediate between a pure GAT expression (which has no wiring layers, but may
have identities, braidings, copies, etc.) and a wiring diagram, which is purely
graphical.
"""
module WiringLayers
export WiringLayer, Layer, input_ports, output_ports, nwires, wires, has_wire,
  add_wire!, add_wires!, rem_wire!, rem_wires!, in_wires, out_wires,
  to_wiring_diagram,
  dom, codom, id, compose, otimes, munit, braid, mcopy, delete, mmerge, create

using AutoHashEquals

using ...GAT, ...Syntax
import ...Doctrines: MonoidalCategoryWithBidiagonals,
  dom, codom, id, compose, otimes, munit, braid, mcopy, delete, mmerge, create
using ..WiringDiagramCore
import ..WiringDiagramCore: input_ports, output_ports, nwires, wires, has_wire,
  add_wire!, add_wires!, rem_wire!, rem_wires!, in_wires, out_wires,
  to_wiring_diagram

# Data types
############

""" Connection by wires of one layer to another.

Morphism in the category of wiring layers.
"""
@auto_hash_equals struct WiringLayer{T}
  wires::Dict{Int}{Dict{Int}{Int}} # src -> tgt -> multiplicity
  input_ports::Vector{T}
  output_ports::Vector{T}

  function WiringLayer(inputs::Vector{T}, outputs::Vector{S}) where {T,S}
    new{promote_type(T,S)}(Dict{Int}{Dict{Int}{Int}}(), inputs, outputs)
  end
end

""" A layer, constituted by a list of ports.

Object in the category of wiring layers.
"""
@auto_hash_equals struct Layer{T}
  ports::Vector{T}
end
Base.eachindex(layer::Layer) = eachindex(layer.ports)
Base.length(layer::Layer) = length(layer.ports)

# Low-level graph interface
###########################

function WiringLayer(wires, inputs, outputs)
  f = WiringLayer(inputs, outputs)
  add_wires!(f, wires)
  f
end

input_ports(f::WiringLayer) = f.input_ports
output_ports(f::WiringLayer) = f.output_ports

has_wire(f::WiringLayer, wire) = nwires(f, wire) > 0

function nwires(f::WiringLayer, wire)
  src, tgt = wire
  get(get(f.wires, src, Dict()), tgt, 0)
end

nwires(f::WiringLayer) = sum(Int[ sum(values(d)) for d in values(f.wires) ])
wires(f::WiringLayer) = vcat((out_wires(f, src) for src in keys(f.wires))...)

function out_wires(f::WiringLayer, src::Int)
  tgts = get(f.wires, src, Dict())
  vcat((repeat([src => tgt], n) for (tgt, n) in tgts)...)
end

function add_wire!(f::WiringLayer, wire)
  check_wire_bounds(f, wire)
  src, tgt = wire
  counts = get!(f.wires, src, Dict{Int}{Int}())
  if haskey(counts, tgt)
    counts[tgt] += 1
  else
    counts[tgt] = 1
  end
end

function add_wires!(f::WiringLayer, wires)
  for wire in wires
    add_wire!(f, wire)
  end
end

function rem_wire!(f::WiringLayer, wire)
  src, tgt = wire
  counts = f.wires[src]
  if counts[tgt] > 1
    counts[tgt] -= 1
  else
    delete!(counts, tgt)
  end
  if isempty(counts)
    delete!(f.wires, src)
  end
end

function rem_wires!(f::WiringLayer, wire)
  src, tgt = wire
  counts = get(f.wires, src, Dict())
  pop!(counts, tgt, nothing)
  if isempty(counts)
    pop!(f.wires, src, nothing)
  end
end

function check_wire_bounds(f::WiringLayer, wire)
  src, tgt = wire
  if !(1 <= src <= length(f.input_ports))
    throw(BoundsError("layer inputs $(f.input_ports)", src))
  end
  if !(1 <= tgt <= length(f.output_ports))
    throw(BoundsError("layer outputs $(f.output_ports)", tgt))
  end
end

# High-level categorical interface
##################################

function WiringLayer(inputs::Layer, outputs::Layer)
  WiringLayer(inputs.ports, outputs.ports)
end

""" Wiring layers as *monoidal category with diagonals and codiagonals*.
"""
@instance MonoidalCategoryWithBidiagonals(Layer, WiringLayer) begin
  dom(f::WiringLayer) = Layer(f.input_ports)
  codom(f::WiringLayer) = Layer(f.output_ports)

  function id(A::Layer)
    f = WiringLayer(A, A)
    add_wires!(f, i=>i for i in eachindex(A))
    f
  end
  
  function compose(f::WiringLayer, g::WiringLayer)
    if codom(f) != dom(g)
      error("Incompatible domains $(codom(f)) and $(dom(g))")
    end
    h = WiringLayer(dom(f), codom(g))
    for (src, mid) in wires(f)
      for (_, tgt) in out_wires(g, mid)
        add_wire!(h, src => tgt)
      end
    end
    h
  end
  
  otimes(A::Layer, B::Layer) = Layer([A.ports; B.ports])
  munit(::Type{Layer}) = Layer([])
  
  function otimes(f::WiringLayer, g::WiringLayer)
    h = WiringLayer(otimes(dom(f),dom(g)), otimes(codom(f),codom(g)))
    m, n = length(dom(f)), length(codom(f))
    add_wires!(h, wires(f))
    add_wires!(h, src+m => tgt+n for (src, tgt) in wires(g))
    h
  end
  
  function braid(A::Layer, B::Layer)
    f = WiringLayer(otimes(A,B), otimes(B,A))
    m, n = length(A), length(B)
    add_wires!(f, i => i+n for i in 1:m)
    add_wires!(f, i+m => i for i in 1:n)
    f
  end

  mcopy(A::Layer) = mcopy(A, 2)
  mmerge(A::Layer) = mmerge(A, 2)
  delete(A::Layer) = WiringLayer(A, munit(Layer))
  create(A::Layer) = WiringLayer(munit(Layer), A)
end

function mcopy(A::Layer, n::Int)
  f = WiringLayer(A, otimes([A for j in 1:n]))
  m = length(A)
  add_wires!(f, i => i+m*(j-1) for i in 1:m, j in 1:n)
  f
end

function mmerge(A::Layer, n::Int)
  f = WiringLayer(otimes([A for j in 1:n]), A)
  m = length(A)
  add_wires!(f, i+m*(j-1) => i for i in 1:m, j in 1:n)
  f
end

# Conversion
############

function to_wiring_diagram(f::WiringLayer)
  diagram = WiringDiagram(input_ports(f), output_ports(f))
  add_wires!(diagram, ((input_id(diagram), src) => (output_id(diagram), tgt)
                       for (src, tgt) in sort!(wires(f))))
  diagram
end

end
