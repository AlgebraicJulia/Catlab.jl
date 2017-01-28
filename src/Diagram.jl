module Diagram
export
  Box, Wires, ConnectorKind, Connector, Connection, AtomicBox, WiringDiagram,
  dom, codom, id, compose, ∘

import Base: eachindex, length
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
eachindex(wires::Wires) = eachindex(wires.wires)
length(wires::Wires) = length(wires.wires)

@enum ConnectorKind Input Output
immutable Connector
  box::Int
  kind::ConnectorKind
  port::Int
end
immutable Connection
  src::Connector
  tgt::Connector
  Connection(src::Connector, tgt::Connector) = new(src, tgt)
  Connection(src::Tuple, tgt::Tuple) = new(Connector(src...), Connector(tgt...))
  Connection(pair::Pair) = Connection(first(pair), last(pair))
end

type AtomicBox <: Box
  content::Any
  dom::Wires
  codom::Wires
end

type WiringDiagram <: Box
  boxes::Array{Box}
  connections::Set{Connection}
  dom::Wires
  codom::Wires
end

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
  reindex(c::Connector) = set_box(c, c.box > subindex ? c.box + length(sub.boxes) : c.box)
  sub_reindex(c::Connector) = set_box(c, c.box + subindex - 1)

  in_conns = filter(c -> c.tgt.box == subindex, diagram.connections)
  in_map = Dict(set_box(c.tgt, 0) => reindex(c.src) for c in in_conns)
  out_conns = filter(c -> c.src.box == subindex, diagram.connections)
  out_map = Dict(set_box(c.src, 0) => reindex(c.tgt) for c in out_conns)

  conns = Set(Connection(reindex(c.src) => reindex(c.tgt))
              for c in diagram.connections if c ∉ in_conns && c ∉ out_conns)
  for conn in sub.connections
    src = conn.src.box == 0 ? in_map[conn.src] : sub_reindex(conn.src)
    tgt = conn.tgt.box == 0 ? out_map[conn.tgt] : sub_reindex(conn.src)
    push!(conns, Connection(src => tgt))
  end
  diagram.connections = conns

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
