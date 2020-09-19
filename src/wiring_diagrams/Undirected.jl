""" Data structure for undirected wiring diagrams.
"""
module UndirectedWiringDiagrams
export UndirectedWiringDiagram, UntypedUWD, TypedUWD,
  outer_box, box, junction, nboxes, njunctions, boxes, junctions,
  ports, ports_with_junction, junction_type, port_type,
  add_box!, add_junction!, add_junctions!, set_junction!, add_wire!,
  add_wires!, singleton_diagram, cospan_diagram, junction_diagram,
  ocompose, substitute

using Compat: isnothing

using ...Present, ...CategoricalAlgebra.CSets, ...CategoricalAlgebra.Limits
using ...CategoricalAlgebra.FinSets: FinSet, FinFunction
using ...Theories: dom, codom, compose, ⋅, id
import ..DirectedWiringDiagrams: box, boxes, nboxes, add_box!, add_wire!,
  add_wires!, singleton_diagram, ocompose, substitute

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
const UntypedUWD = CSetType(TheoryUWD, index=[:box, :junction, :outer_junction])

@present TheoryTypedUWD <: TheoryUWD begin
  Type::Data

  port_type::Attr(Port,Type)
  outer_port_type::Attr(OuterPort,Type)
  junction_type::Attr(Junction,Type)

  compose(junction, junction_type) == port_type
  compose(outer_junction, junction_type) == outer_port_type
end

const AbstractTypedUWD = AbstractACSetType(TheoryTypedUWD)
const TypedUWD = ACSetType(TheoryTypedUWD,
                           index=[:box, :junction, :outer_junction])

function (::Type{UWD})(nports::Int) where UWD <: AbstractUWD
  d = UWD()
  add_parts!(d, :OuterPort, nports)
  return d
end

function (::Type{UWD})(port_types::AbstractVector) where UWD <: AbstractUWD
  d = UWD()
  nports = length(port_types)
  add_parts!(d, :OuterPort, nports, outer_port_type=port_types)
  return d
end

UndirectedWiringDiagram(nports::Int) = UntypedUWD(nports)
UndirectedWiringDiagram(port_types::AbstractVector{T}) where T =
  TypedUWD{T}(port_types)

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

function add_box!(d::AbstractUWD, port_types::AbstractVector; data...)
  box = add_box!(d; data...)
  nports = length(port_types)
  ports = add_parts!(d, :Port, nports, box=fill(box, nports),
                     port_type=port_types)
  box
end

add_junction!(d::AbstractUWD; data...) = add_part!(d, :Junction; data...)
add_junction!(d::AbstractUWD, type; data...) =
  add_part!(d, :Junction; junction_type=type, data...)

add_junctions!(d::AbstractUWD, njunctions::Int; data...) =
  add_parts!(d, :Junction, njunctions; data...)
add_junctions!(d::AbstractUWD, types::AbstractVector; data...) =
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

function singleton_diagram(::Type{UWD}, port_types;
                           data...) where UWD <: AbstractUWD
  d = UWD(port_types)
  add_box!(d, port_types; data...)
  js = add_junctions!(d, port_types)
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
function cospan_diagram(::Type{UWD}, inner::FinFunction{Int},
                        outer::FinFunction{Int}, junction_types=nothing;
                        data...) where UWD <: AbstractUWD
  @assert codom(inner) == codom(outer)
  if isnothing(junction_types)
    junction_types = length(codom(inner))
  end
  cospan_diagram(UWD, collect(inner), collect(outer), junction_types; data...)
end
function cospan_diagram(::Type{UWD}, inner::AbstractVector{Int},
                        outer::AbstractVector{Int}, junction_types;
                        data...) where UWD <: AbstractUWD
  d = UWD(map_port_types(junction_types, outer))
  add_box!(d, map_port_types(junction_types, inner); data...)
  add_junctions!(d, junction_types)
  set_junction!(d, inner)
  set_junction!(d, outer, outer=true)
  return d
end

""" Undirected wiring diagram with no boxes, only junctions.

See also: [`singleton_diagram`](@ref), [`cospan_diagram`](@ref).
"""
function junction_diagram(::Type{UWD}, outer::FinFunction{Int},
                          junction_types=nothing) where UWD <: AbstractUWD
  if isnothing(junction_types)
    junction_types = length(codom(outer))
  end
  junction_diagram(UWD, collect(outer), junction_types)
end
function junction_diagram(::Type{UWD}, outer::AbstractVector{Int},
                          junction_types) where UWD <: AbstractUWD
  d = UWD(map_port_types(junction_types, outer))
  add_junctions!(d, junction_types)
  set_junction!(d, outer, outer=true)
  return d
end

map_port_types(::Int, g) = length(g)
map_port_types(types::AbstractVector, g) = types[g]

# Operadic interface
####################

function ocompose(f::AbstractUWD, gs::AbstractVector{<:AbstractUWD})
  substitute(f, boxes(f), gs)
end
function ocompose(f::AbstractUWD, i::Int, g::AbstractUWD)
  substitute(f, [i], [g])
end

function substitute(f::UWD, indices::AbstractVector{Int},
                    gs::AbstractVector{UWD}) where {UWD <: AbstractUWD}
  @assert length(indices) == length(gs)
  h = UWD()
  copy_parts!(h, f, OuterPort=:)

  # Copy boxes from original diagram and diagrams to be substituted.
  gs_index = Vector{Union{Int,Nothing}}(nothing, nboxes(f))
  gs_index[indices] = 1:length(indices)
  for (i,j) in enumerate(gs_index)
    if isnothing(j)
      copy_parts!(h, f, Box=[i], Port=ports(f, i))
    else
      g = gs[j]
      copy_parts!(h, g, Box=boxes(g), Port=flat(ports(g, boxes(g))))
    end
  end

  # Add junctions obtained from pushout of junction sets.
  f_inner_junction = FinFunction(flat(
    junction(f, ports(f, i)) for (i,j) in enumerate(gs_index) if !isnothing(j)),
    njunctions(f))
  g_outer_junction = oplus([
    FinFunction(junction(g, outer=true), njunctions(g)) for g in gs ])
  f_leg, g_leg = colim = pushout(f_inner_junction, g_outer_junction)
  add_junctions!(h, length(ob(colim)))
  if has_subpart(h, :junction_type)
    # XXX: We should be taking the colimits in a slice category over the
    # junction attributes. That would automate this and also check for errors.
    set_subpart!(h, collect(f_leg), :junction_type, junction_type(f))
    set_subpart!(h, collect(g_leg), :junction_type,
                 flat(junction_type(g) for g in gs))
  end

  # Assign junctions to all ports.
  gs_incl = legs(coproduct([ FinSet(njunctions(g)) for g in gs ]))
  set_junction!(h, map(f_leg, junction(f, outer=true)), outer=true)
  set_junction!(h, flatmap(enumerate(gs_index)) do (i,j)
    if isnothing(j)
      map(f_leg, junction(f, ports(f, i)))
    else
      map(gs_incl[j] ⋅ g_leg, junction(gs[j]))
    end
  end)
  return h
end

flat(x) = reduce(vcat, x, init=Int[])
flatmap(f, xs...) = mapreduce(f, vcat, xs..., init=Int[])

# FIXME: Should be defined in FinSets.
function oplus(fs::AbstractVector{<:FinFunction})
  copair(coproduct(map(dom, fs)), map(compose, fs, coproduct(map(codom, fs))))
end

end
