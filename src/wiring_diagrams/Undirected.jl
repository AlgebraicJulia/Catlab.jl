""" Data structure for undirected wiring diagrams.
"""
module UndirectedWiringDiagrams
export AbstractUndirectedWiringDiagram, UndirectedWiringDiagram,
  outer_box, box, link, nboxes, nlinks, boxes, links, ports, linked_ports,
  link_type, port_type, add_box!, add_link!, add_links!, set_link!, add_wire!,
  add_wires!, ocompose

using ...CategoricalAlgebra.CSets, ...Present
using ...CategoricalAlgebra.ShapeDiagrams: Span
using ...CategoricalAlgebra.FinSets: FinOrdFunction, pushout
using ...Theories: FreeCategory, dom, codom, compose, ⋅, id

import ..DirectedWiringDiagrams: boxes, nboxes, add_box!, add_wire!, add_wires!
import ..AlgebraicWiringDiagrams: ocompose

# Data types
############

@present TheoryUWD(FreeCategory) begin
  Box::Ob
  Port::Ob
  OuterPort::Ob
  Link::Ob

  box::Hom(Port,Box)
  link::Hom(Port,Link)
  outer_link::Hom(OuterPort,Link)
end

const AbstractUndirectedWiringDiagram = const AbstractUWD =
  AbstractCSetType(TheoryUWD)
const UntypedUndirectedWiringDiagram = const UntypedUWD =
  CSetType(TheoryUWD, index=[:box, :link, :outer_link])

@present TheoryTypedUWD <: TheoryUWD begin
  Type::Ob

  port_type::Hom(Port,Type)
  outer_port_type::Hom(OuterPort,Type)
  link_type::Hom(Link,Type)

  compose(link, link_type) == port_type
  compose(outer_link, link_type) == outer_port_type
end

const TypedUndirectedWiringDiagram = const TypedUWD =
  CSetType(TheoryTypedUWD, data=[:Type], index=[:box, :link, :outer_link])

# Imperative interface
######################

function UndirectedWiringDiagram(nports::Int)
  d = UntypedUWD()
  add_parts!(d, :OuterPort, nports)
  return d
end

function UndirectedWiringDiagram(
    ::Type{T}, port_types::AbstractVector{S}) where {T, S<:T}
  d = TypedUWD(port_type=T, outer_port_type=T, link_type=T)
  nports = length(port_types)
  add_parts!(d, :OuterPort, nports, (outer_port_type=port_types,))
  return d
end
UndirectedWiringDiagram(port_types::AbstractVector{T}) where T =
  UndirectedWiringDiagram(T, port_types)

outer_box(::AbstractUWD) = 0
box(d::AbstractUWD, port) = subpart(d, port, :box)
link(d::AbstractUWD, port; outer::Bool=false) =
  subpart(d, port, outer ? :outer_link : :link)

function link(d::AbstractUWD, port::Tuple{Int,Int})
  box, nport = port
  box == outer_box(d) ?
    link(d, nport, outer=true) : link(d, ports(d, box)[nport])
end

nboxes(d::AbstractUWD) = nparts(d, :Box)
nlinks(d::AbstractUWD) = nparts(d, :Link)
boxes(d::AbstractUWD) = 1:nboxes(d)
links(d::AbstractUWD) = 1:nlinks(d)

ports(d::AbstractUWD; outer::Bool=false) =
  1:nparts(d, outer ? :OuterPort : :Port)
ports(d::AbstractUWD, box) =
  box == outer_box(d) ? (1:nparts(d, :OuterPort)) : incident(d, box, :box)
linked_ports(d::AbstractUWD, link; outer::Bool=false) =
  incident(d, link, outer ? :outer_link : :link)

link_type(d::AbstractUWD, link) = subpart(d, link, :link_type)
port_type(d::AbstractUWD, port; outer::Bool=false) =
  subpart(d, port, outer ? :outer_port_type : :port_type)

function port_type(d::AbstractUWD, port::Tuple{Int,Int})
  box, nport = port
  box == outer_box(d) ?
    port_type(d, nport, outer=true) : port_type(d, ports(d, box)[nport])
end

add_box!(d::AbstractUWD; data...) = add_part!(d, :Box, (; data...))

function add_box!(d::AbstractUWD, nports::Int; data...)
  box = add_box!(d; data...)
  ports = add_parts!(d, :Port, nports, (box=box,))
  box
end

function add_box!(d::AbstractUWD, port_types::AbstractVector; data...)
  box = add_box!(d; data...)
  nports = length(port_types)
  ports = add_parts!(d, :Port, nports, (box=box, port_type=port_types))
  box
end

add_link!(d::AbstractUWD) = add_part!(d, :Link)
add_link!(d::AbstractUWD, link_type) = add_part!(d, :Link, (link_type=link_type,))
add_links!(d::AbstractUWD, nlinks::Int) = add_parts!(d, :Link, nlinks)
add_links!(d::AbstractUWD, link_types::AbstractVector) =
  add_parts!(d, :Link, length(link_types), (link_type=link_types,))

function set_link!(d::AbstractUWD, port, link; outer::Bool=false)
  if has_subpart(d, :link_type)
    ptype, ltype = port_type(d, port, outer=outer), link_type(d, link)
    if !all(ptype .== ltype)
      error("Domain error: port type $ptype and link type $ltype do not match")
    end
  end
  set_subpart!(d, port, outer ? :outer_link : :link, link)
end

function set_link!(d::AbstractUWD, port::Tuple{Int,Int}, link)
  box, nport = port
  if box == outer_box(d)
    set_link!(d, nport, link, outer=true)
  else
    set_link!(d, ports(d, box)[nport], link)
  end
end

""" Wire together two ports in an undirected wiring diagram.

A convenience method that creates and sets links as needed. Ports are only
allowed to have one link, so if both ports already have links, then the second
port is assigned the link of the first. The handling of the two arguments is
otherwise symmetric.

FIXME: When both ports already have links, the two links should be *merged*.
To do this, we must implement `merge_links!` and thus also `rem_part!`.
"""
function add_wire!(d::AbstractUWD, port1::Tuple{Int,Int}, port2::Tuple{Int,Int})
  link1, link2 = link(d, port1), link(d, port2)
  if link1 > 0
    set_link!(d, port2, link1)
  elseif link2 > 0
    set_link!(d, port1, link2)
  else
    new_link = has_subpart(d, :link_type) ?
      add_link!(d, port_type(d, port1)) : add_link!(d)
    set_link!(d, port1, new_link)
    set_link!(d, port2, new_link)
  end
end
add_wire!(d, wire::Pair) = add_wire!(d, first(wire), last(wire))

function add_wires!(d::AbstractUWD, wires)
  for wire in wires
    add_wire!(d, wire)
  end
end

# Operadic interface
####################

function ocompose(f::AbstractUWD, i::Int, g::AbstractUWD)
  @assert 1 <= i <= nboxes(f)
  h = empty(f)
  copy_parts!(h, f, (OuterPort=ports(f, outer=true),))
  copy_boxes!(h, f, 1:(i-1))
  copy_boxes!(h, g, boxes(g))
  copy_boxes!(h, f, (i+1):nboxes(f))

  f_i = FinOrdFunction(link(f, ports(f, i)), nlinks(f))
  g_outer = FinOrdFunction(link(g, ports(g, outer=true), outer=true), nlinks(g))
  cospan = pushout(Span(f_i, g_outer))
  f_inc, g_inc = cospan.left, cospan.right
  links = add_links!(h, codom(f_inc).n)
  if has_subpart(h, :link_type)
    set_subpart!(h, [collect(f_inc); collect(g_inc)]
                 :link_type, [link_type(f, :); link_type(g, :)])
  end

  f_outer = FinOrdFunction(link(f, ports(f, outer=true), outer=true), nlinks(f))
  f_start = FinOrdFunction(link(f, flat(ports(f, 1:(i-1)))), nlinks(f))
  g_link = FinOrdFunction(link(g, ports(g)), nlinks(g))
  f_end = FinOrdFunction(link(f, flat(ports(f, (i+1):nboxes(f)))), nlinks(f))
  set_link!(h, :, collect(f_outer ⋅ f_inc), outer=true)
  set_link!(h, :, [
    collect(f_start ⋅ f_inc);
    collect(g_link ⋅ g_inc);
    collect(f_end ⋅ f_inc);
  ])
  return h
end

copy_boxes!(d::AbstractUWD, from::AbstractUWD, boxes) =
  copy_parts!(d, from, (Box=boxes, Port=flat(ports(from, boxes))))

flat(vs) = reduce(vcat, vs, init=Int[])

end
