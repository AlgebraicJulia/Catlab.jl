""" Data structure for undirected wiring diagrams.
"""
module UndirectedWiringDiagrams
export UndirectedWiringDiagram, outer_box, box, junction, nboxes, njunctions,
  boxes, junctions, ports, ports_with_junction, junction_type, port_type,
  add_box!, add_junction!, add_junctions!, set_junction!, add_wire!,
  add_wires!, singleton_diagram, cospan_diagram, junction_diagram, ocompose

using Compat: isnothing

using ...CategoricalAlgebra.CSets, ...Present
using ...CategoricalAlgebra.FinSets: FinFunction
using ...CategoricalAlgebra.Limits: pushout
using ...Theories: FreeSchema, dom, codom, compose, ⋅, id,
  CatDescType, AttrDescType, SchemaType
import ..DirectedWiringDiagrams: box, boxes, nboxes, add_box!, add_wire!,
  add_wires!, singleton_diagram, ocompose

# Data types
############

@present TheoryUWD(FreeSchema) begin
  Box::Ob
  Port::Ob
  OuterPort::Ob
  Junction::Ob

  box::Hom(Port,Box)
  junction::Hom(Port,Junction)
  outer_junction::Hom(OuterPort,Junction)
end

const UndirectedWiringDiagram = const AbstractUWD = AbstractACSetType(TheoryUWD)
const AbstractUntypedUWD = AbstractCSetType(TheoryUWD)
const UntypedUndirectedWiringDiagram = const UntypedUWD =
  CSetType(TheoryUWD, index=[:box, :junction, :outer_junction])

@present TheoryTypedUWD <: TheoryUWD begin
  Type::Data

  port_type::Attr(Port,Type)
  outer_port_type::Attr(OuterPort,Type)
  junction_type::Attr(Junction,Type)

  compose(junction, junction_type) == port_type
  compose(outer_junction, junction_type) == outer_port_type
end

const AbstractTypedUWD = AbstractACSetType(TheoryTypedUWD)
const TypedUndirectedWiringDiagram = ACSetType(TheoryTypedUWD, index=[:box, :junction, :outer_junction])
const TypedUWD = TypedUndirectedWiringDiagram

type_type(::Type{<:TypedUWD{T}}) where {T} = T

function UndirectedWiringDiagram(::Type{UWD}, nports::Int) where UWD <: AbstractUWD
  d = UWD()
  add_parts!(d, :OuterPort, nports)
  return d
end

UndirectedWiringDiagram(nports::Int; kw...) =
  UndirectedWiringDiagram(UntypedUWD, nports; kw...)

function UndirectedWiringDiagram(::Type{UWD},
    port_types::AbstractVector{T}) where {T, UWD <: AbstractUWD}
  d = UWD()
  nports = length(port_types)
  add_parts!(d, :OuterPort, nports, outer_port_type=port_types)
  return d
end

UndirectedWiringDiagram(port_types::AbstractVector{T}; kw...) where {T} =
  UndirectedWiringDiagram(TypedUWD{T}, port_types; kw...)

# Imperative interface
######################

outer_box(::AbstractUWD) = 0
box(d::AbstractUWD, args...) = subpart(d, args..., :box)
junction(d::AbstractUWD, args...; outer::Bool=false) =
  subpart(d, args..., outer ? :outer_junction : :junction)

function junction(d::AbstractUWD, port::Tuple{Int,Int})
  box, nport = port
  box == outer_box(d) ?
    junction(d, nport, outer=true) : junction(d, ports(d, box)[nport])
end

nboxes(d::AbstractUWD) = nparts(d, :Box)
njunctions(d::AbstractUWD) = nparts(d, :Junction)
boxes(d::AbstractUWD) = 1:nboxes(d)
junctions(d::AbstractUWD) = 1:njunctions(d)

ports(d::AbstractUWD; outer::Bool=false) =
  1:nparts(d, outer ? :OuterPort : :Port)
ports(d::AbstractUWD, box) =
  box == outer_box(d) ? (1:nparts(d, :OuterPort)) : incident(d, box, :box)
ports_with_junction(d::AbstractUWD, junction; outer::Bool=false) =
  incident(d, junction, outer ? :outer_junction : :junction)

junction_type(d::AbstractUWD, args...) = subpart(d, args..., :junction_type)
port_type(d::AbstractUWD, args...; outer::Bool=false) =
  subpart(d, args..., outer ? :outer_port_type : :port_type)

function port_type(d::AbstractUWD, port::Tuple{Int,Int})
  box, nport = port
  box == outer_box(d) ?
    port_type(d, nport, outer=true) : port_type(d, ports(d, box)[nport])
end

add_box!(d::AbstractUWD; data...) = add_part!(d, :Box; data...)

function add_box!(d::AbstractUWD, nports::Int; data...)
  box = add_box!(d; data...)
  ports = add_parts!(d, :Port, nports, box=fill(box, nports))
  box
end

function add_box!(d::AbstractUWD, port_types::AbstractVector{T}; data...) where {T}
  box = add_box!(d; data...)
  nports = length(port_types)
  ports = add_parts!(d, :Port, nports, box=fill(box, nports),
                     port_type=port_types)
  box
end

add_junction!(d::AbstractUWD; data...) = add_part!(d, :Junction; data...)
add_junction!(d::AbstractUWD, type::T; data...) where {T} =
  add_part!(d, :Junction; junction_type=type, data...)

add_junctions!(d::AbstractUWD, njunctions::Int; data...) =
  add_parts!(d, :Junction, njunctions; data...)
add_junctions!(d::AbstractUWD, types::AbstractVector{T}; data...) where {T} =
  add_parts!(d, :Junction, length(types); junction_type=types, data...)

function set_junction!(d::AbstractUWD, port, junction; outer::Bool=false)
  if has_subpart(d, :junction_type)
    ptype, jtype = port_type(d, port, outer=outer), junction_type(d, junction)
    all(ptype .== jtype) || error(
      "Domain error: port type $ptype and junction type $jtype do not match")
  end
  set_subpart!(d, port, outer ? :outer_junction : :junction, junction)
end
set_junction!(d::AbstractUWD, junction; kw...) =
  set_junction!(d, :, junction; kw...)

function set_junction!(d::AbstractUWD, port::Tuple{Int,Int}, junction)
  box, nport = port
  if box == outer_box(d)
    set_junction!(d, nport, junction, outer=true)
  else
    set_junction!(d, ports(d, box)[nport], junction)
  end
end

""" Wire together two ports in an undirected wiring diagram.

A convenience method that creates and sets junctions as needed. Ports are only
allowed to have one junction, so if both ports already have junctions, then the
second port is assigned the junction of the first. The handling of the two
arguments is otherwise symmetric.

FIXME: When both ports already have junctions, the two junctions should be
*merged*. To do this, we must implement `merge_junctions!` and thus also
`rem_part!`.
"""
function add_wire!(d::AbstractUWD, port1::Tuple{Int,Int}, port2::Tuple{Int,Int})
  j1, j2 = junction(d, port1), junction(d, port2)
  if j1 > 0
    set_junction!(d, port2, j1)
  elseif j2 > 0
    set_junction!(d, port1, j2)
  else
    j = has_subpart(d, :junction_type) ?
      add_junction!(d, port_type(d, port1)) : add_junction!(d)
    set_junction!(d, port1, j)
    set_junction!(d, port2, j)
  end
end
add_wire!(d, wire::Pair) = add_wire!(d, first(wire), last(wire))

function add_wires!(d::AbstractUWD, wires)
  for wire in wires
    add_wire!(d, wire)
  end
end

# Other constructors
#-------------------

function empty_diagram(::Type{T}, port_types) where T<:AbstractUWD
  UndirectedWiringDiagram((T == AbstractUWD ? () : (T,))..., port_types)
end

function singleton_diagram(::Type{T}, port_types; data...) where T<:AbstractUWD
  d = empty_diagram(T, port_types)
  add_box!(d, port_types; data...)
  js = add_junctions!(d, port_types)
  set_junction!(d, js)
  set_junction!(d, js, outer=true)
  return d
end

function singleton_diagram(::Type{T}, port_types, box_data, junction_data) where T<:AbstractUWD
  d = empty_diagram(T, port_types)
  add_box!(d, port_types; box_data...)
  js = add_junctions!(d, port_types; junction_data...)
  set_junction!(d, js)
  set_junction!(d, js, outer=true)
  return d
end

""" Undirected wiring diagram defined by a cospan.

The wiring diagram has a single box. The ports of this box, the outer ports, the
junctions, and the connections between them are defined by the cospan. Thus,
this function generalizes [`singleton_diagram`](@ref).

See also: [`junction_diagram`](@ref).
"""
function cospan_diagram(::Type{T}, f::FinFunction{Int},
                        f_outer::FinFunction{Int}, junction_types=nothing;
                        data...) where T<:AbstractUWD
  @assert codom(f) == codom(f_outer)
  if isnothing(junction_types); junction_types = length(codom(f)) end
  cospan_diagram(T, collect(f), collect(f_outer), junction_types; data...)
end
function cospan_diagram(::Type{T}, f::AbstractVector{Int},
                        f_outer::AbstractVector{Int}, junction_types;
                        data...) where T<:AbstractUWD
  d = empty_diagram(T, map_port_types(junction_types, f_outer))
  add_box!(d, map_port_types(junction_types, f); data...)
  add_junctions!(d, junction_types)
  set_junction!(d, f)
  set_junction!(d, f_outer, outer=true)
  return d
end

""" Undirected wiring diagram with no boxes, only junctions.

See also: [`singleton_diagram`](@ref), [`cospan_diagram`](@ref).
"""
function junction_diagram(::Type{T}, f::FinFunction{Int},
                          junction_types=nothing) where T<:AbstractUWD
  if isnothing(junction_types); junction_types = length(codom(f)) end
  junction_diagram(T, collect(f), junction_types)
end
function junction_diagram(::Type{T}, f::AbstractVector{Int},
                          junction_types) where T<:AbstractUWD
  d = empty_diagram(T, map_port_types(junction_types, f))
  add_junctions!(d, junction_types)
  set_junction!(d, f, outer=true)
  return d
end

map_port_types(::Int, g) = length(g)
map_port_types(types::AbstractVector, g) = types[g]

# Operadic interface
####################

function ocompose(f::AbstractUWD, gs::AbstractVector{<:AbstractUWD})
  @assert length(gs) == nboxes(f)
  h = empty(f)
  copy_parts!(h, f, OuterPort=:)
  for g in gs
    copy_boxes!(h, g, boxes(g))
  end

  f_junction = FinFunction(
    flat(junction(f, ports(f, i)) for i in boxes(f)), njunctions(f))
  # FIXME: Should use coproduct as monoidal product.
  gs_offset = [0; cumsum(njunctions.(gs))]
  gs_outer = FinFunction(
    flat(junction(g, outer=true) .+ n for (g,n) in zip(gs, gs_offset[1:end-1])),
    gs_offset[end])
  f_inc, g_inc = pushout(f_junction, gs_outer)
  junctions = add_junctions!(h, length(codom(f_inc)))
  if has_subpart(h, :junction_type)
    set_subpart!(h, [collect(f_inc); collect(g_inc)], :junction_type,
                 [junction_type(f); flat(junction_type(g) for g in gs)])
  end

  f_outer = FinFunction(junction(f, outer=true), njunctions(f))
  # FIXME: Again, should use coproduct.
  gs_junction = FinFunction(
    flat(junction(g) .+ n for (g,n) in zip(gs, gs_offset[1:end-1])),
    gs_offset[end])
  set_junction!(h, collect(f_outer ⋅ f_inc), outer=true)
  set_junction!(h, collect(gs_junction ⋅ g_inc))
  return h
end

function ocompose(f::AbstractUWD, i::Int, g::AbstractUWD)
  @assert 1 <= i <= nboxes(f)
  h = empty(f)
  copy_parts!(h, f, OuterPort=:)
  copy_boxes!(h, f, 1:(i-1))
  copy_boxes!(h, g, boxes(g))
  copy_boxes!(h, f, (i+1):nboxes(f))

  f_i = FinFunction(junction(f, ports(f, i)), njunctions(f))
  g_outer = FinFunction(junction(g, outer=true), njunctions(g))
  f_inc, g_inc = pushout(f_i, g_outer)

  if has_subpart(h, :junction_type)
    T = type_type(typeof(h))
    pushout_types = Vector{Union{Missing, T}}(missing, length(codom(f_inc)))
    coproduct_types = [junction_type(f); junction_type(g)]
    for (i,idx) in enumerate([collect(f_inc); collect(g_inc)])
      pushout_types[idx] = coproduct_types[i]
    end
    junctions = add_junctions!(h, Vector{T}(pushout_types))
  else
    junctions = add_junctions!(h, length(codom(f_inc)))
  end

  f_outer = FinFunction(junction(f, outer=true), njunctions(f))
  f_start = FinFunction(junction(f, flat(ports(f, 1:(i-1)))), njunctions(f))
  g_junction = FinFunction(junction(g), njunctions(g))
  f_end = FinFunction(junction(f, flat(ports(f, (i+1):nboxes(f)))),
                      njunctions(f))
  set_junction!(h, collect(f_outer ⋅ f_inc), outer=true)
  set_junction!(h, [
    collect(f_start ⋅ f_inc);
    collect(g_junction ⋅ g_inc);
    collect(f_end ⋅ f_inc);
  ])
  return h
end

copy_boxes!(d::AbstractUWD, from::AbstractUWD, boxes) =
  copy_parts!(d, from, Box=boxes, Port=flat(ports(from, boxes)))

flat(vs) = reduce(vcat, vs, init=Int[])

end
