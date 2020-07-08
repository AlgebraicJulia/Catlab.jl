""" Data structure for undirected wiring diagrams.
"""
module UndirectedWiringDiagrams
export AbstractUndirectedWiringDiagram, UndirectedWiringDiagram,
  box, link, nboxes, nlinks, boxes, links, ports, linked_ports,
  outer_id, outer_link, outer_ports, linked_outer_ports,
  add_box!, add_link!, add_links!, set_link!, set_outer_link!

using ...CategoricalAlgebra.CSets, ...Present
using ...Theories: FreeCategory

import ..DirectedWiringDiagrams: boxes, nboxes, add_box!

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

UndirectedWiringDiagram(port_types::AbstractVector{T}) where T =
  UndirectedWiringDiagram(T, port_types)

function UndirectedWiringDiagram(
    ::Type{T}, port_types::AbstractVector{S}) where {T, S<:T}
  d = TypedUWD(port_type=T, outer_port_type=T, link_type=T)
  nports = length(port_types)
  add_parts!(d, :OuterPort, nports, (outer_port_type=port_types,))
  return d
end

box(d::AbstractUWD, port) = subpart(d, port, :box)
link(d::AbstractUWD, port) = subpart(d, port, :link)

function link(d::AbstractUWD, port::Tuple)
  box, nport = port
  box == outer_id(d) ? outer_link(d, nport) : link(d, ports(d, box)[nport])
end

nboxes(d::AbstractUWD) = nparts(d, :Box)
nlinks(d::AbstractUWD) = nparts(d, :Link)
boxes(d::AbstractUWD) = 1:nboxes(d)
links(d::AbstractUWD) = 1:nlinks(d)
ports(d::AbstractUWD) = 1:nparts(d, :Port)
ports(d::AbstractUWD, box) = incident(d, box, :box)
linked_ports(d::AbstractUWD, link) = incident(d, link, :link)

outer_id(::AbstractUWD) = 0
outer_link(d::AbstractUWD, outer_port) = subpart(d, outer_port, :outer_link)
outer_ports(d::AbstractUWD) = 1:nparts(d, :OuterPort)
linked_outer_ports(d::AbstractUWD, outer_port) =
  incident(d, outer_port, :outer_link)

add_box!(d::AbstractUWD; data...) = add_part!(d, :Box, (; data...))

function add_box!(d::AbstractUWD, nports::Int; data...)
  box = add_box!(d; data...)
  ports = add_parts!(d, :Port, nports, (box=box,))
  (box, ports)
end

function add_box!(d::AbstractUWD, port_types::AbstractVector; data...)
  box = add_box!(d; data...)
  nports = length(port_types)
  ports = add_parts!(d, :Port, nports, (box=box, port_type=port_types))
  (box, ports)
end

add_link!(d::AbstractUWD) = add_part!(d, :Link)
add_link!(d::AbstractUWD, link_type) = add_part!(d, :Link, (link_type=link_type))
add_links!(d::AbstractUWD, nlinks::Int) = add_parts!(d, :Link, nlinks)
add_links!(d::AbstractUWD, link_types::AbstractVector) =
  add_parts!(d, :Link, length(link_types), (link_type=link_types,))

set_link!(d::AbstractUWD, port, link) = set_subpart!(d, port, :link, link)
set_link!(d::AbstractUWD, box, port, link) =
  set_link!(d, ports(d, box)[port], link)
set_outer_link!(d::AbstractUWD, outer_port, link) =
  set_subpart!(d, outer_port, :outer_link, link)

end
