""" Wiring diagrams as a symmetric monoidal category and as an operad.

This module provides a high-level functional and algebraic interface to wiring
diagrams, built on top of the lower-level imperative interface.
"""
module AlgebraicWiringDiagrams
export Junction, dom, codom, id, compose, otimes, munit, braid, mcopy, delete,
  mmerge, create, permute, ocompose, add_junctions!, rem_junctions!

using AutoHashEquals

using ...GAT, ...Syntax
import ...Doctrines:
  ObExpr, HomExpr, MonoidalCategoryWithBidiagonals, dom, codom, id, compose,
  otimes, munit, braid, mcopy, delete, mmerge, create, dunit, dcounit
using ..WiringDiagramCore, ..WiringLayers
import ..WiringDiagramCore: Box, WiringDiagram, Ports,
  input_ports, output_ports, add_box!

# Data types
############

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

# Categorical interface
#######################

""" Create box for a morphism generator.
"""
function Box(expr::HomExpr{:generator})
  Box(first(expr), collect_values(dom(expr)), collect_values(codom(expr)))
end
add_box!(f::WiringDiagram, expr::HomExpr) = add_box!(f, Box(expr))

""" Create empty wiring diagram with given domain and codomain objects.
"""
function WiringDiagram(inputs::ObExpr, outputs::ObExpr)
  WiringDiagram(Ports(inputs), Ports(outputs))
end
Ports(expr::ObExpr) = Ports(collect_values(expr))

function collect_values(ob::ObExpr)::Vector
  exprs = collect(ob)
  @assert all(head(expr) == :generator for expr in exprs)
  return map(first, exprs)
end

""" Wiring diagrams as a monoidal category with diagonals and codiagonals.
"""
@instance MonoidalCategoryWithBidiagonals(Ports, WiringDiagram) begin
  dom(f::WiringDiagram) = Ports(f.input_ports)
  codom(f::WiringDiagram) = Ports(f.output_ports)
  
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
  
  otimes(A::Ports, B::Ports) = Ports([A.ports; B.ports])
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

  mcopy(A::Ports) = mcopy(A, 2)
  mmerge(A::Ports) = mmerge(A, 2)
  delete(A::Ports) = WiringDiagram(A, munit(Ports))
  create(A::Ports) = WiringDiagram(munit(Ports), A)
end

# Unbiased variants of braiding (permutation), copying, and merging.

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
  f = WiringDiagram(munit(Ports), otimes(A,A))
  n = length(A)
  for (i, port) in enumerate(A.ports)
    v = add_box!(f, Junction(port, 0, 2))
    add_wires!(f, ((v,1) => (output_id(f),i), (v,2) => (output_id(f),i+n)))
  end
  return f
end

function dcounit(A::Ports)
  f = WiringDiagram(otimes(A,A), munit(Ports))
  n = length(A)
  for (i, port) in enumerate(A.ports)
    v = add_box!(f, Junction(port, 2, 0))
    add_wires!(f, ((input_id(f),i) => (v,1), (input_id(f),i+n) => (v,2)))
  end
  return f
end

# Operadic interface
####################

""" Operadic composition of wiring diagrams.

This generic function has two different signatures, corresponding to the two
standard definitions of an operad (Yau, 2018, Operads of Wiring Diagrams,
Definitions 2.3 and 2.10).

This operation is a simple wrapper around substitution (`substitute`).
"""
function ocompose(f::WiringDiagram, gs::Vector{WiringDiagram})
  @assert length(gs) == nboxes(f)
  substitute(f, box_ids(f), gs)
end
function ocompose(f::WiringDiagram, i::Int, g::WiringDiagram)
  @assert 1 <= i <= nboxes(f)
  substitute(f, box_ids(f)[i], g)
end

# Junctions
###########

""" Add junction nodes to wiring diagram.

Transforms from the implicit to the explicit representation of diagonals and
codiagonals. This operation is inverse to `rem_junctions!`.
"""
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
codiagonals. This operation is inverse to `add_junctions!`.

Note: This function does not actually mutate its argument. However, this is
subject to change in the future.
"""
function rem_junctions!(d::WiringDiagram)
  junction_ids = filter(v -> box(d,v) isa Junction, box_ids(d))
  junction_diagrams = map(junction_ids) do v
    junction = box(d,v)::Junction
    layer = complete_layer(junction.ninputs, junction.noutputs)
    to_wiring_diagram(layer, input_ports(junction), output_ports(junction))
  end
  substitute(d, junction_ids, junction_diagrams)
end

end
