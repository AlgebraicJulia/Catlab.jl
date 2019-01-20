""" Conventions for serialization of wiring diagrams.

Defines a consistent set of names for boxes, ports, and wires to be used when
serializing wiring diagrams.
"""
module WiringDiagramSerialization
export box_id, wire_id, port_name

using ..WiringDiagramCore

function box_id(path::Vector{Int})::String
  if isempty(path)
    "root"
  else
    prod(["n$v" for v in path])
  end
end
function box_id(diagram::WiringDiagram, path::Vector{Int})
  v = last(path)
  if v == input_id(diagram) || v == output_id(diagram)
    box_id(path[1:end-1])
  else
    box_id(path)
  end
end

function wire_id(path::Vector{Int}, wire::Int)::String
  if isempty(path)
    string("e", wire)
  else
    string(box_index(path), "e", wire)
  end
end

function port_name(kind::PortKind, port::Int)
  string(kind == InputPort ? "in" : "out", port)
end
function port_name(diagram::WiringDiagram, port::Port)
  kind = if port.box == input_id(diagram)
    InputPort
  elseif port.box == output_id(diagram)
    OutputPort
  else
    port.kind
  end
  port_name(kind, port.port)
end

end