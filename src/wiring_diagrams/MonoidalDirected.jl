""" Wiring diagrams as a symmetric monoidal category.

This module provides a high-level categorical interface to wiring diagrams,
building on the low-level imperative interface and the operadic interface. It
also defines data types and functions to represent diagonals, codiagonals,
duals, caps, cups, daggers, and other gadgets in wiring diagrams.
"""
module MonoidalDirectedWiringDiagrams
export Ports, Junction, PortOp, BoxOp, functor, permute,
  implicit_mcopy, implicit_mmerge, junctioned_mcopy, junctioned_mmerge,
  junction_diagram, add_junctions, add_junctions!, rem_junctions, merge_junctions,
  junction_caps, junction_cups, junctioned_dunit, junctioned_dcounit

using StructEquality

using ...GAT, ...Theories
import ...Theories: dom, codom, id, compose, ⋅, ∘,
  otimes, ⊗, munit, braid, σ, oplus, ⊕, mzero, swap,
  mcopy, delete, Δ, ◊, mmerge, create, ∇, □, dual, dunit, dcounit, mate, dagger,
  plus, zero, coplus, cozero, meet, join, top, bottom, trace
import ...Syntax: functor, head
using ...Graphs
using ..DirectedWiringDiagrams
import ..DirectedWiringDiagrams: Box, WiringDiagram, input_ports, output_ports, value
import ..UndirectedWiringDiagrams: add_junctions!, junction_diagram

# Categorical interface
#######################

# Ports as objects
#-----------------

""" A list of ports.

The objects in categories of wiring diagrams.
"""
@struct_hash_equal struct Ports{Theory,Value}
  ports::Vector{Value}
  Ports{T}(ports::Vector{V}) where {T,V} = new{T,V}(ports)
end
Ports(ports::Vector) = Ports{Any}(ports)

# Iterator interface.
Base.iterate(A::Ports, args...) = iterate(A.ports, args...)
Base.keys(A::Ports) = keys(A.ports)
Base.length(A::Ports) = length(A.ports)
Base.eltype(A::Ports{T,V}) where {T,V} = V

# Indexing interface.
Base.getindex(A::Ports, i::Int) = A.ports[i]
Base.getindex(A::Ports{T}, i::UnitRange) where T = Ports{T}(A.ports[i])
Base.firstindex(A::Ports) = 1
Base.lastindex(A::Ports) = length(A)

Base.cat(A::Ports{T}, B::Ports{T}) where T = Ports{T}([A.ports; B.ports])
Base.reverse(A::Ports{T}) where T = Ports{T}(reverse(A.ports))

Box(value, inputs::Ports, outputs::Ports) =
  Box(value, collect(inputs), collect(outputs))
Box(inputs::Ports, outputs::Ports) = Box(collect(inputs), collect(outputs))

WiringDiagram(value, inputs::Ports{T}, outputs::Ports{T}) where T =
  WiringDiagram{T}(value, collect(inputs), collect(outputs))

WiringDiagram(inputs::Ports{T}, outputs::Ports{T}) where T =
  WiringDiagram{T}(collect(inputs), collect(outputs))

dom(d::WiringDiagram{T}) where T = Ports{T}(input_ports(d))
codom(d::WiringDiagram{T}) where T = Ports{T}(output_ports(d))

# Symmetric monoidal category
#----------------------------

""" Wiring diagrams as a symmetric monoidal category.

Extra structure, such as copying or merging, can be added to wiring diagrams in
different ways, but wiring diagrams always form a symmetric monoidal category in
the same way.
"""
@instance ThSymmetricMonoidalCategory{Ports, WiringDiagram} begin
  @import dom, codom

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

function permute(A::Ports{T}, σ::Vector{Int}; inverse::Bool=false) where T
  @assert length(A) == length(σ)
  B = Ports{T}([ A[σ[i]] for i in eachindex(σ) ])
  if inverse
    f = WiringDiagram(B, A)
    add_wires!(f, ((input_id(f),σ[i]) => (output_id(f),i) for i in eachindex(σ)))
  else
    f = WiringDiagram(A, B)
    add_wires!(f, ((input_id(f),i) => (output_id(f),σ[i]) for i in eachindex(σ)))
  end
  return f
end

# Functors
#---------

""" Apply functor in a category of wiring diagrams.

Defined by compatible mappings of ports and boxes.
"""
function functor(d::WiringDiagram, f_ports, f_box; contravariant::Bool=false, kw...)
  functor_impl = contravariant ? contravariant_functor : covariant_functor
  functor_impl(d, f_ports, f_box; kw...)
end

function covariant_functor(d::WiringDiagram, f_ports, f_box)
  result = WiringDiagram(f_ports(dom(d)), f_ports(codom(d)))
  add_boxes!(result, (f_box(box(d, v)) for v in box_ids(d)))
  add_wires!(result, wires(d))
  result
end

function contravariant_functor(d::WiringDiagram, f_ports, f_box;
                               monoidal_contravariant::Bool=false)
  result = WiringDiagram(f_ports(codom(d)), f_ports(dom(d)))
  add_boxes!(result, (f_box(box(d, v)) for v in box_ids(d)))

  nports = (port::Port) -> length(
    (port.kind == InputPort ? input_ports : output_ports)(d, port.box))
  map_port = (port::Port) -> Port(
    if (port.box == input_id(d)) output_id(d)
    elseif (port.box == output_id(d)) input_id(d)
    else port.box end,
    port.kind == InputPort ? OutputPort : InputPort,
    monoidal_contravariant ? nports(port) - port.port + 1 : port.port
  )
  add_wires!(result, map(wires(d)) do wire
    Wire(wire.value, map_port(wire.target), map_port(wire.source))
  end)
  result
end

# Diagonals and codiagonals
#--------------------------

""" Implicit copy in wiring diagram.

Copies are represented by multiple outgoing wires from a single port and
deletions by no outgoing wires.
"""
function implicit_mcopy(A::Ports, n::Int)
  f = WiringDiagram(A, otimes(repeat([A], n)))
  m = length(A)
  add_wires!(f, ((input_id(f),i) => (output_id(f),i+m*(j-1))
                  for i in 1:m for j in 1:n))
  return f
end

""" Implicit merge in wiring diagram.

Merges are represented by multiple incoming wires into a single port and
creations by no incoming wires.
"""
function implicit_mmerge(A::Ports, n::Int)
  f = WiringDiagram(otimes(repeat([A],n)), A)
  m = length(A)
  add_wires!(f, ((input_id(f),i+m*(j-1)) => (output_id(f),i)
                  for i in 1:m for j in 1:n))
  return f
end

""" Explicit copy in wiring diagram.

Copies and deletions are represented by junctions (boxes of type `Junction`).
"""
junctioned_mcopy(A::Ports, n::Int; kw...) = junction_diagram(A, 1, n; kw...)

""" Explicit merge in wiring diagram.

Merges and creations are represented by junctions (boxes of type `Junction`).
"""
junctioned_mmerge(A::Ports, n::Int; kw...) = junction_diagram(A, n, 1; kw...)

# Implicit diagonals and codiagonals are the default in untyped wiring diagrams.
mcopy(A::Ports{Any}, n::Int) = implicit_mcopy(A, n)
mmerge(A::Ports{Any}, n::Int) = implicit_mmerge(A, n)

# Default implementation for biased (co)diagonals fall backs to unbiased
# (co)diagonals, if they are defined.
mcopy(A::Ports) = mcopy(A, 2)
delete(A::Ports) = mcopy(A, 0)
mmerge(A::Ports) = mmerge(A, 2)
create(A::Ports) = mmerge(A, 0)
plus(A::Ports) = plus(A, 2)
zero(A::Ports) = plus(A, 0)
coplus(A::Ports) = coplus(A, 2)
cozero(A::Ports) = coplus(A, 0)

# Cartesian category
#-------------------

mcopy(A::Ports{ThMonoidalCategoryWithDiagonals}, n::Int) = implicit_mcopy(A, n)

mcopy(A::Ports{ThCartesianCategory}, n::Int) = implicit_mcopy(A, n)

# Cocartesian category
#---------------------

mmerge(A::Ports{ThMonoidalCategoryWithCodiagonals}, n::Int) = implicit_mmerge(A, n)

mmerge(A::Ports{ThCocartesianCategory}, n::Int) = implicit_mmerge(A, n)

# Biproduct category
#-------------------

# The coherence laws relating diagonal to codiagonal do not hold for general
# bidiagonals, so an explicit representation is needed.
mcopy(A::Ports{ThMonoidalCategoryWithBidiagonals}, n::Int) = junctioned_mcopy(A, n)
mmerge(A::Ports{ThMonoidalCategoryWithBidiagonals}, n::Int) = junctioned_mmerge(A, n)

mcopy(A::Ports{ThBiproductCategory}, n::Int) = implicit_mcopy(A, n)
mmerge(A::Ports{ThBiproductCategory}, n::Int) = implicit_mmerge(A, n)

# Dagger category
#----------------

dagger(f::WiringDiagram{ThDaggerSymmetricMonoidalCategory}) =
  functor(f, identity, dagger, contravariant=true)

# Compact closed category
#------------------------

junctioned_dunit(A::Ports) = junction_caps(A, otimes(dual(A),A))
junctioned_dcounit(A::Ports) = junction_cups(A, otimes(A,dual(A)))

dual(A::Ports{ThCompactClosedCategory}) = dual_ports(A)
dunit(A::Ports{ThCompactClosedCategory}) = junctioned_dunit(A)
dcounit(A::Ports{ThCompactClosedCategory}) = junctioned_dcounit(A)
mate(f::WiringDiagram{ThCompactClosedCategory}) =
  functor(f, dual, mate, contravariant=true, monoidal_contravariant=true)

dual(A::Ports{ThDaggerCompactCategory}) = dual_ports(A)
dunit(A::Ports{ThDaggerCompactCategory}) = junctioned_dunit(A)
dcounit(A::Ports{ThDaggerCompactCategory}) = junctioned_dcounit(A)
dagger(f::WiringDiagram{ThDaggerCompactCategory}) =
  functor(f, identity, dagger, contravariant=true)
mate(f::WiringDiagram{ThDaggerCompactCategory}) =
  functor(f, dual, mate, contravariant=true, monoidal_contravariant=true)

# Traced monoidal category
#-------------------------

""" Trace (feedback loop) in a wiring diagram.
"""
function trace(X::Ports, f::WiringDiagram; unsubstituted::Bool=false)
  n = length(X)
  @assert dom(f)[1:n] == X && codom(f)[1:n] == X
  A, B = dom(f)[n+1:end], codom(f)[n+1:end]
  h = WiringDiagram(A, B)
  fv = add_box!(h, f)
  add_wires!(h, (fv,i) => (fv,i) for i in 1:n)
  add_wires!(h, (input_id(h),i) => (fv,i+n) for i in eachindex(A))
  add_wires!(h, (fv,i+n) => (output_id(h),i) for i in eachindex(B))
  unsubstituted ? h : substitute(h)
end

const TracedMon = ThTracedMonoidalCategory

trace(X::Ports{TracedMon}, A::Ports{TracedMon},
      B::Ports{TracedMon}, f::WiringDiagram{TracedMon}) = trace(X, f)

# Bicategory of relations
#------------------------

const BiRel = ThBicategoryRelations

mcopy(A::Ports{BiRel}, n::Int) = junctioned_mcopy(A, n)
mmerge(A::Ports{BiRel}, n::Int) = junctioned_mmerge(A, n)

dunit(A::Ports{BiRel}) = junction_caps(A)
dcounit(A::Ports{BiRel}) = junction_cups(A)

dagger(f::WiringDiagram{BiRel}) =
  functor(f, identity, dagger, contravariant=true)

meet(f::WiringDiagram{BiRel}, g::WiringDiagram{BiRel}) =
  compose(mcopy(dom(f)), otimes(f,g), mmerge(codom(f)))
top(A::Ports{BiRel}, B::Ports{BiRel}) = compose(delete(A), create(B))

# Abelian bicategory of relations
#--------------------------------

const AbBiRel = ThAbelianBicategoryRelations

# Additive notation. FIXME: Use @instance.
oplus(f::WiringDiagram{AbBiRel}, g::WiringDiagram{AbBiRel}) = otimes(f,g)
⊕(f::WiringDiagram{AbBiRel}, g::WiringDiagram{AbBiRel}) = oplus(f,g)
mzero(::Type{T}) where T <: Ports{AbBiRel} = munit(T)
swap(A::Ports{AbBiRel}, B::Ports{AbBiRel}) = braid(A, B)

mcopy(A::Ports{AbBiRel}, n::Int) = junctioned_mcopy(A, n; op=:times)
mmerge(A::Ports{AbBiRel}, n::Int) = junctioned_mmerge(A, n; op=:times)

dunit(A::Ports{AbBiRel}) = junction_caps(A; op=:times)
dcounit(A::Ports{AbBiRel}) = junction_cups(A; op=:times)

plus(A::Ports{AbBiRel}, n::Int) = junctioned_mmerge(A, n, op=:plus)
coplus(A::Ports{AbBiRel}, n::Int) = junctioned_mcopy(A, n, op=:plus)

dagger(f::WiringDiagram{AbBiRel}) =
  functor(f, identity, dagger, contravariant=true)

meet(f::WiringDiagram{AbBiRel}, g::WiringDiagram{AbBiRel}) =
  compose(mcopy(dom(f)), oplus(f,g), mmerge(codom(f)))
join(f::WiringDiagram{AbBiRel}, g::WiringDiagram{AbBiRel}) =
  compose(coplus(dom(f)), oplus(f,g), plus(codom(f)))
top(A::Ports{AbBiRel}, B::Ports{AbBiRel}) = compose(delete(A), create(B))
bottom(A::Ports{AbBiRel}, B::Ports{AbBiRel}) = compose(cozero(A), zero(B))

# Junctions
###########

""" Junction node in a wiring diagram.

Junction nodes are used to explicitly represent copies, merges, deletions,
creations, caps, and cups.
"""
struct Junction{Op,Value} <: AbstractBox
  value::Value
  input_ports::Vector
  output_ports::Vector
end

Junction(args...) = Junction{nothing}(args...)
Junction{Op}(value::Value, inputs::Vector, outputs::Vector) where {Op,Value} =
  Junction{Op,Value}(value, inputs, outputs)
Junction{Op}(value, ninputs::Int, noutputs::Int) where Op = 
  Junction{Op}(value, repeat([value], ninputs), repeat([value], noutputs))

head(junction::Junction{Op}) where Op = Op

Base.:(==)(j1::Junction, j2::Junction) =
  head(j1) == head(j2) && struct_equal(j1, j2)

""" Wiring diagram with a junction node for each of the given ports.
"""
junction_diagram(A::Ports, nin::Int, nout::Int; op=nothing) =
  junction_diagram(Junction{op}, A, nin, nout)

function junction_diagram(make_junction, A::Ports, nin::Int, nout::Int)
  f = WiringDiagram(otimes(repeat([A], nin)), otimes(repeat([A], nout)))
  m = length(A)
  for (i, value) in enumerate(A)
    v = add_box!(f, make_junction(
      value, repeat([value], nin), repeat([value], nout)))
    add_wires!(f, ((input_id(f),i+m*(j-1)) => (v,j) for j in 1:nin))
    add_wires!(f, ((v,j) => (output_id(f),i+m*(j-1)) for j in 1:nout))
  end
  return f
end

""" Wiring diagram of nested cups made out of junction nodes.
"""
junction_cups(A::Ports; kw...) = junction_cups(A, cat(A,reverse(A)); kw...)
junction_cups(A::Ports, inputs::Ports; op=nothing) =
  junction_cups(Junction{op}, A, inputs)

function junction_cups(make_junction, A::Ports, inputs::Ports)
  @assert length(inputs) == 2*length(A)
  f = WiringDiagram(inputs, munit(typeof(inputs)))
  m, ports = length(A), collect(inputs)
  for (i, value) in enumerate(A)
    j1, j2 = i, 2m-i+1 # Outer cups to inner cups
    v = add_box!(f, make_junction(value, ports[[j1,j2]], empty(ports)))
    add_wires!(f, [(input_id(f),j1) => (v,1), (input_id(f),j2) => (v,2)])
  end
  return f
end

""" Wiring diagram of nested caps made out of junction nodes.
"""
junction_caps(A::Ports; kw...) = junction_caps(A, cat(reverse(A),A); kw...)
junction_caps(A::Ports, outputs::Ports; op=nothing) =
  junction_caps(Junction{op}, A, outputs)

function junction_caps(make_junction, A::Ports, outputs::Ports)
  @assert length(outputs) == 2*length(A)
  f = WiringDiagram(munit(typeof(outputs)), outputs)
  m, ports = length(A), collect(outputs)
  for (i, value) in enumerate(A)
    j1, j2 = m-i+1, m+i # Inner caps to outer caps
    v = add_box!(f, make_junction(value, empty(ports), ports[[j1,j2]]))
    add_wires!(f, [(v,1) => (output_id(f),j1), (v,2) => (output_id(f),j2)])
  end
  return f
end

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
      sources = sort!([ wire.source for wire in wires ])
      add_wire!(d, Port(jv, OutputPort, 1) => Port(v, InputPort, port))
      add_wires!(d, [ source => Port(jv, InputPort, i)
                      for (i, source) in enumerate(sources) ])
    end
  end
end

function add_output_junctions!(d::WiringDiagram, v::Int)
  for (port, port_value) in enumerate(output_ports(d, v))
    # TODO: Sort out wires.
    wires = out_wires(d, v, port)
    nwires = length(wires)
    if nwires != 1
      rem_wires!(d, wires)
      jv = add_box!(d, Junction(port_value, 1, nwires))
      targets = sort!([ wire.target for wire in wires ])
      add_wire!(d, Port(v, OutputPort, port) => Port(jv, InputPort, 1))
      add_wires!(d, [ Port(jv, OutputPort, i) => target
                      for (i, target) in enumerate(targets) ])
    end
  end
end

""" Remove junction nodes from wiring diagram.

Transforms from the explicit to the implicit representation of diagonals and
codiagonals. This operation is inverse to `add_junctions`.
"""
function rem_junctions(d::WiringDiagram; op=nothing)
  junction_ids = filter(v -> box(d,v) isa Junction{op}, box_ids(d))
  junction_diagrams = map(junction_ids) do v
    junction = box(d,v)::Junction
    inputs, outputs = input_ports(junction), output_ports(junction)
    wiring = WiringDiagram(inputs, outputs)
    add_wires!(wiring, (input_id(wiring), src) => (output_id(wiring), tgt)
                        for src in eachindex(inputs), tgt in eachindex(outputs))
    wiring
  end
  substitute(d, junction_ids, junction_diagrams)
end

""" Merge adjacent junction nodes into single junctions.
"""
function merge_junctions(d::WiringDiagram; op=nothing)
  junction_graph = Graph(nboxes(d))
  for wire in wires(d, :Wire)
    src, tgt = wire.source.box, wire.target.box
    if (d.diagram[src, :box_type] <: Junction &&
        d.diagram[tgt, :box_type] <: Junction &&
        d.diagram[src, :value] == d.diagram[tgt, :value])
      add_edge!(junction_graph, src, tgt)
    end
  end

  components = filter(c -> length(c) > 1, connected_components(junction_graph))
  values = [ d.diagram[first(component), :value] for component in components ]
  encapsulate(d, components;
    discard_boxes=true, values=values, make_box=Junction{op})
end

# Operations on ports and boxes
###############################

""" Port value wrapping another value.

Represents unary operations on ports in wiring diagrams.
"""
struct PortOp{Op}
  value::Any
end

head(::PortOp{Op}) where Op = Op

Base.:(==)(op1::PortOp, op2::PortOp) =
  head(op1) == head(op2) && struct_equal(op1, op2)

""" Box wrapping another box.

Represents unary operations on boxes in wiring diagrams.
"""
struct BoxOp{Op} <: AbstractBox
  box::AbstractBox
end
BoxOp{Op}(value::Value, inputs::Vector, outputs::Vector) where {Op,Value} =
  BoxOp{Op}(Box{Value}(value, outputs, inputs))

head(::BoxOp{Op}) where Op = Op
input_ports(op::BoxOp) = input_ports(op.box)
output_ports(op::BoxOp) = output_ports(op.box)
value(op::BoxOp) = value(op.box)

Base.:(==)(op1::BoxOp, op2::BoxOp) =
  head(op1) == head(op2) && struct_equal(op1, op2)

# Duals
#------

const DualPort = PortOp{:dual}

dual_port(x) = DualPort(x)
dual_port(dual::DualPort) = dual.value

dual_ports(ports::Vector) = [ dual_port(x) for x in Iterators.reverse(ports) ]
dual_ports(ports::Ports{T}) where T = Ports{T}(dual_ports(collect(ports)))

# Adjoints
#---------

const DaggerBox = BoxOp{:dagger}
DaggerBox(value::Value, inputs::Vector, outputs::Vector) where Value =
  DaggerBox(Box{Value}(value, outputs, inputs))

input_ports(dagger::DaggerBox) = output_ports(dagger.box)
output_ports(dagger::DaggerBox) = input_ports(dagger.box)

dagger(box::Box) = DaggerBox(box)
dagger(dagger::DaggerBox) = dagger.box
dagger(junction::Junction{Op}) where Op = Junction{Op}(
  junction.value, output_ports(junction), input_ports(junction))

const MateBox = BoxOp{:mate}
MateBox(value::Value, inputs::Vector, outputs::Vector) where Value = 
  MateBox(Box{Value}(value, dual_ports(outputs), dual_ports(inputs)))

input_ports(mate::MateBox) = dual_ports(output_ports(mate.box))
output_ports(mate::MateBox) = dual_ports(input_ports(mate.box))

mate(box::Box) = MateBox(box)
mate(mate::MateBox) = mate.box

# Assume that mates and daggers commute, as in a dagger compact category.
# Normalize to apply mates before daggers.
dagger(mate::MateBox) = DaggerBox(mate)
mate(dagger::DaggerBox) = dagger(mate(dagger.box))

end
