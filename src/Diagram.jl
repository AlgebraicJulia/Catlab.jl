module Diagram
export
  Box, Wires, ConnectorKind, Connector, Connection, AtomicBox, WiringDiagram,
  dom, codom, id, compose, ∘,
  otimes, munit, ⊗

import Base: ==, eachindex, length, show
using Typeclass

import ..Doctrine:
  Category, dom, codom, id, compose, ∘,
  MonoidalCategory, otimes, munit, ⊗

# Diagrams
##########

""" TODO: Document
"""
abstract Box

immutable Wires
  wires::Array
  Wires(wires...) = new(collect(wires))
end
==(w1::Wires, w2::Wires) = w1.wires == w2.wires
eachindex(wires::Wires) = eachindex(wires.wires)
length(wires::Wires) = length(wires.wires)

@enum ConnectorKind Input Output
immutable Connector
  box::Int
  kind::ConnectorKind
  port::Int
end
show(io::IO, c::Connector) = print(io, "($(c.box),$(c.kind),$(c.port))")

immutable Connection
  src::Connector
  tgt::Connector
  Connection(src::Connector, tgt::Connector) = new(src, tgt)
  Connection(src::Tuple, tgt::Tuple) = new(Connector(src...), Connector(tgt...))
  Connection(pair::Pair) = Connection(first(pair), last(pair))
end
show(io::IO, c::Connection) = print(io, "$(c.src)=>$(c.tgt)")

type AtomicBox <: Box
  content::Any
  dom::Wires
  codom::Wires
end
==(b1::AtomicBox, b2::AtomicBox) =
  b1.content == b2.content && b1.dom == b2.dom && b1.codom == b2.codom
show(io::IO, box::AtomicBox) = print(io, "Box($(repr(box.content)))")

type WiringDiagram <: Box
  boxes::Array{Box}
  connections::Set{Connection}
  dom::Wires
  codom::Wires
end
==(b1::WiringDiagram, b2::WiringDiagram) =
  b1.boxes == b2.boxes && b1.connections == b2.connections &&
  b1.dom == b2.dom && b1.codom == b2.codom
show(io::IO, box::WiringDiagram) =
  print(io, "WiringDiagram($(box.boxes),$(box.connections))")

""" Flatten a wiring diagram.
"""
function flatten!(diagram::WiringDiagram)::WiringDiagram
  for (i,box) in enumerate(diagram.boxes)
    if isa(box, WiringDiagram)
      return flatten!(flatten!(diagram, i))
    end
  end
  return diagram
end

function flatten!(diagram::WiringDiagram, subindex::Int)
  # Flatten boxes.
  sub = diagram.boxes[subindex]::WiringDiagram
  splice!(diagram.boxes, subindex, sub.boxes)

  # Flatten connections.
  set_box(c::Connector, box::Int) = Connector(box, c.kind, c.port)
  reindex(c::Connector) =
    set_box(c, c.box > subindex ? c.box + length(sub.boxes) - 1 : c.box)
  sub_reindex(c::Connector) = set_box(c, c.box + subindex - 1)

  in_map = Dict(set_box(c.tgt, 0) => c.src
                for c in diagram.connections if c.tgt.box == subindex)
  out_map = Dict(set_box(c.src, 0) => c.tgt
                 for c in diagram.connections if c.src.box == subindex)
  connections = Set(Connection(reindex(c.src) => reindex(c.tgt))
                    for c in diagram.connections
                    if c.src.box != subindex && c.tgt.box != subindex)
  for c in sub.connections
    src = c.src.box == 0 ? reindex(in_map[c.src]) : sub_reindex(c.src)
    tgt = c.tgt.box == 0 ? reindex(out_map[c.tgt]) : sub_reindex(c.tgt)
    push!(connections, Connection(src => tgt))
  end
  diagram.connections = connections
  return diagram
end

# Category
##########

@instance! Category Wires Box begin
  dom(f::Box) = f.dom
  codom(f::Box) = f.codom
  id(A::Wires) = AtomicBox(:id, A, A)

  function compose(f::Box, g::Box)
    if codom(f) != dom(g)
      error("Incompatible domains $(codom(f)) and $(dom(f))")
    end
    boxes = [f,g]
    connections = union(
      Set(Connection((0,Input,i) => (1,Input,i)) for i in eachindex(f.dom)),
      Set(Connection((1,Output,i) => (2,Input,i)) for i in eachindex(f.codom)),
      Set(Connection((2,Output,i) => (0,Output,i)) for i in eachindex(g.codom))
    )
    flatten!(WiringDiagram(boxes, connections, dom(f), codom(g)))
  end
end

# Monoidal category
###################

@instance! MonoidalCategory Wires Box begin
  otimes(A::Wires, B::Wires) = Wires([A.wires; B.wires]...)
  function otimes(f::Box, g::Box)
    m, n = length(f.dom), length(f.codom)
    boxes = [f,g]
    connections = union(
      Set(Connection((0,Input,i) => (1,Input,i)) for i in eachindex(f.dom)),
      Set(Connection((0,Input,i+m) => (2,Input,i)) for i in eachindex(g.dom)),
      Set(Connection((1,Output,i) => (0,Output,i)) for i in eachindex(f.codom)),
      Set(Connection((2,Output,i) => (0,Output,i+n)) for i in eachindex(g.codom))
    )
    flatten!(WiringDiagram(
      boxes, connections, otimes(dom(f),dom(g)), otimes(codom(f),codom(g))))
  end
  munit(::Wires) = Wires()
end

end
