module TestGraphMLWiringDiagrams

using Test
using LightXML
using Catlab.Doctrines
using Catlab.WiringDiagrams

# Test round trip of wiring diagrams with dictionary box and wire data.

function roundtrip(f::WiringDiagram)
  xdoc = write_graphml(f)
  read_graphml(Dict, Nothing, Dict, xdoc)
end

ports(n::Int) = repeat([nothing], n)
diagram = WiringDiagram(ports(1), ports(1))
f = Box(Dict("name" => "f", "type" => "foo"), ports(1), ports(1))
fv = add_box!(diagram, f)
add_wires!(diagram, [
  Wire(Dict("name" => "w1", "type" => "woo"),
      (input_id(diagram), 1) => (fv, 1)),
  Wire(Dict("name" => "w2", "type" => "woo"),
       (fv, 1) => (output_id(diagram), 1)),
])
@test roundtrip(diagram) == diagram

# Test round trip of wiring diagrams with symbolic box and port values.

function roundtrip_symbolic(f::WiringDiagram)
  xdoc = write_graphml(f)
  read_graphml(Symbol, Symbol, Nothing, xdoc)
end

A, B, C = Ob(FreeSymmetricMonoidalCategory, :A, :B, :C)
f = WiringDiagram(Hom(:f, A, B))
g = WiringDiagram(Hom(:g, B, C))

@test roundtrip_symbolic(f) == f
@test roundtrip_symbolic(compose(f,g)) == compose(f,g)
@test roundtrip_symbolic(otimes(f,g)) == otimes(f,g)

end
