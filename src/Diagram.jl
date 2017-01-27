module Diagram
export
  Box, Wires, ConnectorKind, Connector, Connection, AtomicBox, WiringDiagram,
  dom, codom, id, compose, ∘

using Typeclass
using ..Doctrine: Category, MonoidalCategory

# Diagrams
##########

""" TODO: Document
"""
abstract Box
immutable Wires
  wires::Array
end

@enum ConnectorKind Input Output
immutable Connector
  box::Int
  kind::ConnectorKind
  port::Int
end
immutable Connection
  src::Connector
  tgt::Connector
  Connection(src::Tuple, tgt::Tuple) = new(Connector(src...), Connector(tgt...))
end

type AtomicBox <: Box
  content::Any
  dom::Wires
  codom::Wires
end

type WiringDiagram <: Box
  boxes::Array{Box}
  connections::Array{Connection}
  dom::Wires
  codom::Wires
end

""" Wrap a single box with a wiring diagram.
"""
function wrap_box(box::Box)::WiringDiagram
  connections = append(
    [ Connection((0,Input,i),(1,Input,i)) for i in eachindex(box.dom) ],
    [ Connection((1,Output,i),(0,Output,i)) for i in eachindex(box.codom) ]
  )
  WiringDiagram([box], connections, dom(box), codom(box))
end

""" Convert a box to a wiring diagram if it is not already.
"""
to_wiring_diagram(box::Box) = is(box, WiringDiagram) ? box : wrap_box(box)

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
    f, g = map(to_wiring_diagram, (f, g))
    wd = WiringDiagram([], [], dom(f), codom(g))
  end
end

end
