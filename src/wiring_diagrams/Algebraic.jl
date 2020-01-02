""" Wiring diagrams as a symmetric monoidal category and as an operad.

This module provides a high-level functional and algebraic interface to wiring
diagrams, building on the low-level imperative interface. It also defines data
types and functions to represent diagonals, codiagonals, units, and counits in
wiring diagrams as special *junction nodes*.
"""
module AlgebraicWiringDiagrams
export Ports, dom, codom, id, compose, ⋅, ∘, otimes, ⊗, munit, braid, permute,
  mcopy, delete, Δ, ◇, mmerge, create, ∇, □, dunit, dcounit, ocompose,
  Junction, add_junctions, add_junctions!, rem_junctions, merge_junctions

using AutoHashEquals
using LightGraphs

using ...GAT, ...Syntax
import ...Doctrines: SymmetricMonoidalCategory,
  dom, codom, id, compose, ⋅, ∘, otimes, ⊗, munit, braid,
  mcopy, delete, Δ, ◇, mmerge, create, ∇, □, dunit, dcounit
using ..WiringDiagramCore, ..WiringLayers
import ..WiringDiagramCore: Box, WiringDiagram, input_ports, output_ports

# Categorical interface
#######################

# Ports
#------

""" A list of ports.

The objects in categories of wiring diagrams.
"""
@auto_hash_equals struct Ports{Theory,Value}
  ports::Vector{Value}
  Ports{T}(ports::Vector{V}) where {T,V} = new{T,V}(ports)
end
Ports(ports::Vector) = Ports{Any}(ports)

# Iterator interface.
Base.iterate(A::Ports, args...) = iterate(A.ports, args...)
Base.keys(A::Ports) = keys(A.ports)
Base.length(A::Ports) = length(A.ports)
Base.eltype(A::Ports{T,V}) where {T,V} = V

Base.cat(A::Ports{T}, B::Ports{T}) where T = Ports{T}([A.ports; B.ports])

Box(value, inputs::Ports, outputs::Ports) =
  Box(value, collect(inputs), collect(outputs))
Box(inputs::Ports, outputs::Ports) = Box(collect(inputs), collect(outputs))

WiringDiagram(value, inputs::Ports{T}, outputs::Ports{T}) where T =
  WiringDiagram{T}(value, collect(inputs), collect(outputs))

WiringDiagram(inputs::Ports{T}, outputs::Ports{T}) where T =
  WiringDiagram{T}(collect(inputs), collect(outputs))

input_ports(::Type{Ports}, d::WiringDiagram{T}) where T = Ports{T}(input_ports(d))
output_ports(::Type{Ports}, d::WiringDiagram{T}) where T = Ports{T}(output_ports(d))

# Symmetric monoidal category
#----------------------------

""" Wiring diagrams as a symmetric monoidal category.

Extra structure, such as copying or merging, can be added to wiring diagrams in
different ways, but wiring diagrams always form a symmetric monoidal category in
the same way.
"""
@instance SymmetricMonoidalCategory(Ports, WiringDiagram) begin
  dom(f::WiringDiagram) = input_ports(Ports, f)
  codom(f::WiringDiagram) = output_ports(Ports, f)

  function id(A::Ports)
    f = WiringDiagram(A, A)
    add_wires!(f, ((input_id(f),i) => (output_id(f),i) for i in eachindex(A)))
    return f
  end

  function compose(f::WiringDiagram, g::WiringDiagram; unsubstituted::Bool=false)
    if length(codom(f)) != length(dom(g))
      # Check only that f and g have the same number of ports.
      # The port types will be checked when the wires are added.
      error("Incompatible domains $(codom(f)) and $(dom(g))")
    end
    h = WiringDiagram(dom(f), codom(g))
    fv = add_box!(h, f)
    gv = add_box!(h, g)
    add_wires!(h, ((input_id(h),i) => (fv,i) for i in eachindex(dom(f))))
    add_wires!(h, ((fv,i) => (gv,i) for i in eachindex(codom(f))))
    add_wires!(h, ((gv,i) => (output_id(h),i) for i in eachindex(codom(g))))
    unsubstituted ? h : substitute(h, [fv,gv])
  end

  otimes(A::Ports, B::Ports) = cat(A, B)
  munit(::Type{Ports}) = Ports([])

  function otimes(f::WiringDiagram, g::WiringDiagram; unsubstituted::Bool=false)
    h = WiringDiagram(otimes(dom(f),dom(g)), otimes(codom(f),codom(g)))
    m, n = length(dom(f)), length(codom(f))
    fv = add_box!(h, f)
    gv = add_box!(h, g)
    add_wires!(h, (input_id(h),i) => (fv,i) for i in eachindex(dom(f)))
    add_wires!(h, (input_id(h),i+m) => (gv,i) for i in eachindex(dom(g)))
    add_wires!(h, (fv,i) => (output_id(h),i) for i in eachindex(codom(f)))
    add_wires!(h, (gv,i) => (output_id(h),i+n) for i in eachindex(codom(g)))
    unsubstituted ? h : substitute(h, [fv,gv])
  end

  function braid(A::Ports, B::Ports)
    h = WiringDiagram(otimes(A,B), otimes(B,A))
    m, n = length(A), length(B)
    add_wires!(h, ((input_id(h),i) => (output_id(h),i+n) for i in 1:m))
    add_wires!(h, ((input_id(h),i+m) => (output_id(h),i) for i in 1:n))
    h
  end
end

munit(::Type{Ports{T}}) where T = Ports{T}([])
munit(::Type{Ports{T,V}}) where {T,V} = Ports{T}(V[])

# Unbiased version of braiding (permutation).

function permute(A::Ports, σ::Vector{Int}; inverse::Bool=false)
  @assert length(A) == length(σ)
  B = Ports([ A.ports[σ[i]] for i in eachindex(σ) ])
  if inverse
    f = WiringDiagram(B, A)
    add_wires!(f, ((input_id(f),σ[i]) => (output_id(f),i) for i in eachindex(σ)))
  else
    f = WiringDiagram(A, B)
    add_wires!(f, ((input_id(f),i) => (output_id(f),σ[i]) for i in eachindex(σ)))
  end
  return f
end

# Diagonals and codiagonals
#--------------------------

mcopy(A::Ports) = mcopy(A, 2)
mmerge(A::Ports) = mmerge(A, 2)
delete(A::Ports) = WiringDiagram(A, munit(typeof(A)))
create(A::Ports) = WiringDiagram(munit(typeof(A)), A)

function mcopy(A::Ports, n::Int)::WiringDiagram
  f = WiringDiagram(A, otimes([A for j in 1:n]))
  m = length(A)
  for j in 1:n
    add_wires!(f, ((input_id(f),i) => (output_id(f),i+m*(j-1)) for i in 1:m))
  end
  return f
end

function mmerge(A::Ports, n::Int)::WiringDiagram
  f = WiringDiagram(otimes([A for j in 1:n]), A)
  m = length(A)
  for j in 1:n
    add_wires!(f, ((input_id(f),i+m*(j-1)) => (output_id(f),i) for i in 1:m))
  end
  return f
end

# Wiring diagrams as self-dual compact closed category.
# FIXME: What about compact categories that are not self-dual?

function dunit(A::Ports)
  f = WiringDiagram(munit(typeof(A)), otimes(A,A))
  n = length(A)
  for (i, value) in enumerate(A)
    v = add_box!(f, Junction(value, 0, 2))
    add_wires!(f, ((v,1) => (output_id(f),i), (v,2) => (output_id(f),i+n)))
  end
  return f
end

function dcounit(A::Ports)
  f = WiringDiagram(otimes(A,A), munit(typeof(A)))
  n = length(A)
  for (i, value) in enumerate(A)
    v = add_box!(f, Junction(value, 2, 0))
    add_wires!(f, ((input_id(f),i) => (v,1), (input_id(f),i+n) => (v,2)))
  end
  return f
end

# Operadic interface
####################

""" Operadic composition of wiring diagrams.

This generic function has two different signatures, corresponding to the two
standard definitions of an operad (Yau, 2018, *Operads of Wiring Diagrams*,
Definitions 2.3 and 2.10).

This operation is a simple wrapper around substitution (`substitute`).
"""
function ocompose(f::WiringDiagram, gs::Vector{<:WiringDiagram})
  @assert length(gs) == nboxes(f)
  substitute(f, box_ids(f), gs)
end
function ocompose(f::WiringDiagram, i::Int, g::WiringDiagram)
  @assert 1 <= i <= nboxes(f)
  substitute(f, box_ids(f)[i], g)
end

# Junctions
###########

""" Junction node in a wiring diagram.

Junction nodes are used to explicitly represent copies, merges, deletions,
creations, caps, and cups.
"""
@auto_hash_equals struct Junction{Value} <: AbstractBox
  value::Value
  ninputs::Int
  noutputs::Int
end
input_ports(junction::Junction) = repeat([junction.value], junction.ninputs)
output_ports(junction::Junction) = repeat([junction.value], junction.noutputs)

""" Add junction nodes to wiring diagram.

Transforms from the implicit to the explicit representation of diagonals and
codiagonals. This operation is inverse to `rem_junctions`.
"""
function add_junctions(d::WiringDiagram)
  add_junctions!(copy(d))
end
function add_junctions!(d::WiringDiagram)
  add_output_junctions!(d, input_id(d))
  add_input_junctions!(d, output_id(d))
  for v in box_ids(d)
    add_input_junctions!(d, v)
    add_output_junctions!(d, v)
  end
  return d
end

function add_input_junctions!(d::WiringDiagram, v::Int)
  for (port, port_value) in enumerate(input_ports(d, v))
    wires = in_wires(d, v, port)
    nwires = length(wires)
    if nwires != 1
      rem_wires!(d, wires)
      jv = add_box!(d, Junction(port_value, nwires, 1))
      add_wire!(d, Port(jv, OutputPort, 1) => Port(v, InputPort, port))
      add_wires!(d, [ wire.source => Port(jv, InputPort, i)
                      for (i, wire) in enumerate(wires) ])
    end
  end
end

function add_output_junctions!(d::WiringDiagram, v::Int)
  for (port, port_value) in enumerate(output_ports(d, v))
    wires = out_wires(d, v, port)
    nwires = length(wires)
    if nwires != 1
      rem_wires!(d, wires)
      jv = add_box!(d, Junction(port_value, 1, nwires))
      add_wire!(d, Port(v, OutputPort, port) => Port(jv, InputPort, 1))
      add_wires!(d, [ Port(jv, OutputPort, i) => wire.target
                      for (i, wire) in enumerate(wires) ])
    end
  end
end

""" Remove junction nodes from wiring diagram.

Transforms from the explicit to the implicit representation of diagonals and
codiagonals. This operation is inverse to `add_junctions`.
"""
function rem_junctions(d::WiringDiagram)
  junction_ids = filter(v -> box(d,v) isa Junction, box_ids(d))
  junction_diagrams = map(junction_ids) do v
    junction = box(d,v)::Junction
    layer = complete_layer(junction.ninputs, junction.noutputs)
    to_wiring_diagram(layer, input_ports(junction), output_ports(junction))
  end
  substitute(d, junction_ids, junction_diagrams)
end

""" Merge adjacent junction nodes into single junctions.
"""
function merge_junctions(d::WiringDiagram)
  junction_ids = filter(v -> box(d,v) isa Junction, box_ids(d))
  junction_graph, vmap = induced_subgraph(graph(d), junction_ids)
  components = [ [ vmap[v] for v in component ]
    for component in weakly_connected_components(junction_graph)
    if length(component) > 1 ]
  values = map(components) do component
    values = unique(box(d,v).value for v in component)
    @assert length(values) == 1
    first(values)
  end
  encapsulate(d, components; discard_boxes=true, values=values,
    make_box = (value, in, out) -> Junction(value, length(in), length(out)))
end

end
