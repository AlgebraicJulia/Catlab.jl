""" The category of abstract wiring diagrams (aka string diagrams).

"Abstract" means that they cannot be directly rendered as raster or vector
graphics. However, they form a useful intermediate representation that can be
straightforwardly translated into Graphviz, TikZ, and other declarative diagram
languages.
"""
module AbstractWiring
export
  Wires, Box, WiringDiagram, wires, box,
  ConnectorKind, Input, Output, Connector, Connection,
  dom, codom, id, compose, ∘,
  otimes, munit, ⊗

import Base: eachindex, length, show
using AutoHashEquals
using Typeclass

import ...Doctrine:
  Category, dom, codom, id, compose, ∘,
  MonoidalCategory, otimes, munit, ⊗

# Wiring Diagrams
#################

abstract BaseBox

""" Object in the category of wiring diagrams.
"""
@auto_hash_equals immutable Wires
  wires::Vector
end
wires(wires...) = Wires(collect(wires))
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

""" Atomic or generator box with no internal structure.
"""
@auto_hash_equals type Box <: BaseBox
  content::Any
  dom::Wires
  codom::Wires
end
dom(box::Box) = box.dom
codom(box::Box) = box.codom
show(io::IO, box::Box) = print(io, "Box($(repr(box.content)))")

""" Morphism in the category of wiring diagrams.
"""
@auto_hash_equals type WiringDiagram <: BaseBox
  boxes::Vector{BaseBox}
  connections::Set{Connection}
  dom::Wires
  codom::Wires
end
show(io::IO, box::WiringDiagram) =
  print(io, "WiringDiagram($(box.boxes),$(box.connections))")

""" A wiring diagram with a single inner Box.

These are the generators of the category of wiring diagrams.
"""
function box(content, dom::Wires, codom::Wires)
  inner = Box(content, dom, codom)
  connections = union(
    Set(Connection((0,Input,i) => (1,Input,i)) for i in eachindex(dom)),
    Set(Connection((1,Output,i) => (0,Output,i)) for i in eachindex(codom))
  )
  WiringDiagram([inner], connections, dom, codom)
end

""" Completely flatten a wiring diagram.
"""
function flatten(diagram::WiringDiagram)::WiringDiagram
  for (i,box) in enumerate(diagram.boxes)
    if isa(box, WiringDiagram)
      return flatten(flatten(diagram, i))
    end
  end
  return diagram
end

""" Flatten a single wiring diagram inside another wiring diagram.
"""
function flatten(diagram::WiringDiagram, subindex::Int)
  # Flatten boxes.
  sub = diagram.boxes[subindex]::WiringDiagram
  boxes = copy(diagram.boxes)
  splice!(boxes, subindex, sub.boxes)

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

  WiringDiagram(boxes, connections, dom(diagram), codom(diagram))
end

# Category
##########

@instance! Category Wires WiringDiagram begin
  dom(f::WiringDiagram) = f.dom
  codom(f::WiringDiagram) = f.codom
  
  function id(A::Wires)
    connections = Set(
      Connection((0,Input,i) => (0,Output,i)) for i in eachindex(A))
    WiringDiagram([], connections, A, A)
  end

  function compose(f::WiringDiagram, g::WiringDiagram)
    if codom(f) != dom(g)
      error("Incompatible domains $(codom(f)) and $(dom(f))")
    end
    boxes = [f,g]
    connections = union(
      Set(Connection((0,Input,i) => (1,Input,i)) for i in eachindex(f.dom)),
      Set(Connection((1,Output,i) => (2,Input,i)) for i in eachindex(f.codom)),
      Set(Connection((2,Output,i) => (0,Output,i)) for i in eachindex(g.codom))
    )
    flatten(WiringDiagram(boxes, connections, dom(f), codom(g)))
  end
end

# Monoidal category
###################

@instance! MonoidalCategory Wires WiringDiagram begin
  otimes(A::Wires, B::Wires) = Wires([A.wires; B.wires])
  
  function otimes(f::WiringDiagram, g::WiringDiagram)
    m, n = length(f.dom), length(f.codom)
    boxes = [f,g]
    connections = union(
      Set(Connection((0,Input,i) => (1,Input,i)) for i in eachindex(f.dom)),
      Set(Connection((0,Input,i+m) => (2,Input,i)) for i in eachindex(g.dom)),
      Set(Connection((1,Output,i) => (0,Output,i)) for i in eachindex(f.codom)),
      Set(Connection((2,Output,i) => (0,Output,i+n)) for i in eachindex(g.codom))
    )
    flatten(WiringDiagram(
      boxes, connections, otimes(dom(f),dom(g)), otimes(codom(f),codom(g))))
  end
  
  munit(::Wires) = Wires([])
end

end
