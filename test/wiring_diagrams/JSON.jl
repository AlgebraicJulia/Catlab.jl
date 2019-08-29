module TestJSONWiringDiagrams

using Test
import JSON
using Catlab.Doctrines
using Catlab.WiringDiagrams

# Round trip wiring diagrams with dictionary box and wire data.

function roundtrip(f::WiringDiagram)
  json = sprint(JSON.print, generate_json_graph(f), 2)
  parse_json_graph(Dict, Nothing, Dict, JSON.parse(json))
end

ports(n) = Nothing[ nothing for i in 1:n ]
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

# Round trip wiring diagrams with symbolic box and port values.

function roundtrip_symbolic(f::WiringDiagram)
  json = sprint(JSON.print, generate_json_graph(f), 2)
  parse_json_graph(Symbol, Symbol, Nothing, JSON.parse(json))
end

A, B, C = Ob(FreeSymmetricMonoidalCategory, :A, :B, :C)
f = WiringDiagram(Hom(:f, A, B))
g = WiringDiagram(Hom(:g, B, C))

@test roundtrip_symbolic(f) == f
@test roundtrip_symbolic(compose(f,g)) == compose(f,g)
@test roundtrip_symbolic(otimes(f,g)) == otimes(f,g)

# Round trip nested, symbolic wiring diagrams.

f = WiringDiagram(Hom(:f, A, B))
diagram = WiringDiagram(:outer, [:A], [:B])
fv = add_box!(diagram, f)
add_wires!(diagram, [
  Wire((input_id(diagram),1) => (fv,1)),
  Wire((fv,1) => (output_id(diagram),1))
])
@test roundtrip_symbolic(diagram) == diagram

end
