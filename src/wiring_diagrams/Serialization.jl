""" Conventions for serialization of wiring diagrams.

Defines a consistent set of names for boxes, ports, and wires to be used when
serializing wiring diagrams, as well as conventions for serializing box, port,
and wire attributes.
"""
module WiringDiagramSerialization
export box_id, wire_id, port_name,
  convert_from_graph_data, convert_to_graph_data

using ..WiringDiagramCore

# Identifiers
#############

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
    string(box_id(path), "e", wire)
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

# Attributes
############

convert_from_graph_data(::Type{Nothing}, data::AbstractDict) = nothing
convert_from_graph_data(::Type{T}, data::AbstractDict) where T <: AbstractDict =
  convert(T, data)

function convert_from_graph_data(Value::Type, data::AbstractDict)
  @assert length(data) == 1
  convert(Value, first(values(data)))
end
function convert_from_graph_data(::Type{Symbol}, data::AbstractDict)
  @assert length(data) == 1
  Symbol(first(values(data)))
end

convert_to_graph_data(::Nothing) = Dict()
convert_to_graph_data(value::AbstractDict) = value
convert_to_graph_data(value) = Dict("value" => value)

end
