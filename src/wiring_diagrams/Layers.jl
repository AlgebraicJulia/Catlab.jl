""" Data structure for connecting one layer to another by wires.

This module defines a generic data structure to represent a wiring between one
layer of input ports and another layer of output ports. A wiring layer forms a
bipartite graph with independent edge sets the input ports and the output ports.

Wiring layers are an auxillary data structure. They are not very interesting in
their own right, but they can be a useful intermediate representation. For
example, a morphism expression comprising generators, compositions, products,
and wiring layers is intermediate between a pure GAT expression (which has no
wiring layers, but may have identities, braidings, copies, etc.) and a wiring
diagram, which is purely graphical.
"""
module WiringLayers
export WiringLayer, NLayer, nwires, wires, has_wire, add_wire!, add_wires!,
  rem_wire!, rem_wires!, in_wires, out_wires,
  complete_layer, to_wiring_diagram, wiring_layer_between,
  dom, codom, id, compose, otimes, munit, braid, mcopy, delete, mmerge, create

using AutoHashEquals
using DataStructures: OrderedDict

using ...GAT, ...Syntax
import ...Doctrines: ObExpr, HomExpr, MonoidalCategoryWithBidiagonals,
  dom, codom, id, compose, otimes, munit, braid, mcopy, delete, mmerge, create
using ..WiringDiagramCore
import ..WiringDiagramCore: nwires, wires, has_wire, add_wire!, add_wires!,
  rem_wire!, rem_wires!, in_wires, out_wires

# Data types
############

""" Connection by wires of one layer to another.

Morphism in the category of wiring layers.
"""
@auto_hash_equals struct WiringLayer
  wires::OrderedDict{Int}{OrderedDict{Int}{Int}} # src -> tgt -> multiplicity
  ninputs::Int
  noutputs::Int
  function WiringLayer(ninputs::Int, noutputs::Int)
    new(OrderedDict{Int}{OrderedDict{Int}{Int}}(), ninputs, noutputs)
  end
end

""" Number of input or output ports in a layer.

Object in the category of wiring layers.
"""
@auto_hash_equals struct NLayer
  n::Int
end

# Imperative interface
######################

# Constructors.

WiringLayer(inputs::NLayer, outputs::NLayer) = WiringLayer(inputs.n, outputs.n)

function WiringLayer(wires, ninputs, noutputs)
  f = WiringLayer(ninputs, noutputs)
  add_wires!(f, wires)
  f
end

""" Completely connected wiring layer.

The layer's underlying graph is the complete bipartite graph.
"""
function complete_layer(ninputs::Int, noutputs::Int)
  f = WiringLayer(ninputs, noutputs)
  add_wires!(f, i=>j for j in 1:noutputs for i in 1:ninputs)
  f
end

# Basic accessors.

has_wire(f::WiringLayer, wire) = nwires(f, wire) > 0

function nwires(f::WiringLayer, wire)
  src, tgt = wire
  tgts = get(f.wires, src) do; Dict() end
  get(tgts, tgt, 0)
end

nwires(f::WiringLayer) = sum(Int[ sum(values(d)) for d in values(f.wires) ])
wires(f::WiringLayer) = vcat((out_wires(f, src) for src in keys(f.wires))...)

function out_wires(f::WiringLayer, src::Int)
  tgts = get(f.wires, src) do; Dict() end
  vcat((repeat([src => tgt], n) for (tgt, n) in tgts)...)
end

# Layer mutation.

function add_wire!(f::WiringLayer, wire)
  check_wire_bounds(f, wire)
  src, tgt = wire
  tgts = get!(f.wires, src) do; OrderedDict{Int}{Int}() end
  if haskey(tgts, tgt)
    tgts[tgt] += 1
  else
    tgts[tgt] = 1
  end
end

function add_wires!(f::WiringLayer, wires)
  for wire in wires
    add_wire!(f, wire)
  end
end

function rem_wire!(f::WiringLayer, wire)
  src, tgt = wire
  tgts = f.wires[src]
  if tgts[tgt] > 1
    tgts[tgt] -= 1
  else
    delete!(tgts, tgt)
  end
  if isempty(tgts)
    delete!(f.wires, src)
  end
end

function rem_wires!(f::WiringLayer, wire)
  src, tgt = wire
  tgts = get(f.wires, src) do; Dict() end
  pop!(tgts, tgt, nothing)
  if isempty(tgts)
    pop!(f.wires, src, nothing)
  end
end

function check_wire_bounds(f::WiringLayer, wire)
  src, tgt = wire
  if !(1 <= src <= f.ninputs)
    throw(BoundsError("layer inputs 1:$(f.ninputs)", src))
  end
  if !(1 <= tgt <= f.noutputs)
    throw(BoundsError("layer outputs 1:$(f.noutputs)", tgt))
  end
end

# Categorical interface
#######################

NLayer(ob::ObExpr) = NLayer(ndims(ob))
WiringLayer(inputs::ObExpr, outputs::ObExpr) =
  WiringLayer(ndims(inputs), ndims(outputs))

""" Wiring layers as *monoidal category with diagonals and codiagonals*.
"""
@instance MonoidalCategoryWithBidiagonals(NLayer, WiringLayer) begin
  dom(f::WiringLayer) = NLayer(f.ninputs)
  codom(f::WiringLayer) = NLayer(f.noutputs)

  function id(A::NLayer)
    f = WiringLayer(A, A)
    add_wires!(f, i=>i for i in 1:A.n)
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

  otimes(A::NLayer, B::NLayer) = NLayer(A.n + B.n)
  munit(::Type{NLayer}) = NLayer(0)

  function otimes(f::WiringLayer, g::WiringLayer)
    h = WiringLayer(otimes(dom(f),dom(g)), otimes(codom(f),codom(g)))
    m, n = dom(f).n, codom(f).n
    add_wires!(h, wires(f))
    add_wires!(h, src+m => tgt+n for (src, tgt) in wires(g))
    h
  end

  function braid(A::NLayer, B::NLayer)
    f = WiringLayer(otimes(A,B), otimes(B,A))
    add_wires!(f, i => i+B.n for i in 1:A.n)
    add_wires!(f, i+A.n => i for i in 1:B.n)
    f
  end

  mcopy(A::NLayer) = mcopy(A, 2)
  mmerge(A::NLayer) = mmerge(A, 2)
  delete(A::NLayer) = WiringLayer(A, munit(NLayer))
  create(A::NLayer) = WiringLayer(munit(NLayer), A)
end

function mcopy(A::NLayer, n::Int)
  f = WiringLayer(A, otimes([A for j in 1:n]))
  add_wires!(f, i => i+A.n*(j-1) for i in 1:A.n, j in 1:n)
  f
end

function mmerge(A::NLayer, n::Int)
  f = WiringLayer(otimes([A for j in 1:n]), A)
  add_wires!(f, i+A.n*(j-1) => i for i in 1:A.n, j in 1:n)
  f
end

# Wiring diagrams
#################

""" Convert a wiring layer into a wiring diagram.
"""
function to_wiring_diagram(layer::WiringLayer, inputs::Vector, outputs::Vector)
  @assert length(inputs) == layer.ninputs && length(outputs) == layer.noutputs
  diagram = WiringDiagram(inputs, outputs)
  add_wires!(diagram, ((input_id(diagram), src) => (output_id(diagram), tgt)
                       for (src, tgt) in sort!(wires(layer))))
  diagram
end

""" Wiring layer representing the wires between two boxes in a wiring diagram.
"""
function wiring_layer_between(diagram::WiringDiagram, v1::Int, v2::Int)::WiringLayer
  inputs, outputs = output_ports(diagram, v1), input_ports(diagram, v2)
  layer = WiringLayer(length(inputs), length(outputs))
  add_wires!(layer, (wire.source.port => wire.target.port
                     for wire in wires(diagram, v1, v2)))
  layer
end

end
