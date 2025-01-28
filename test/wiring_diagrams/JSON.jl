module TestJSONWiringDiagrams
using Test

using Catlab.Theories, Catlab.WiringDiagrams

function roundtrip(BoxT, PortT, WireT, f::WiringDiagram)
  mktempdir() do dir
    path = joinpath(dir, "dwd.json")
    write_json_graph(f, path, indent=2)
    read_json_graph(BoxT, PortT, WireT, path)
  end
end

# Round trip wiring diagrams with dictionary box and wire data.

ports(n) = Nothing[ nothing for i in 1:n ]
diagram = WiringDiagram(ports(1), ports(1))
f = Box(Dict(:name => "f", :type => "foo"), ports(1), ports(1))
fv = add_box!(diagram, f)
add_wires!(diagram, [
  Wire(Dict(:name => "w1", :type => "woo"),
      (input_id(diagram), 1) => (fv, 1)),
  Wire(Dict(:name => "w2", :type => "woo"),
       (fv, 1) => (output_id(diagram), 1)),
])
@test roundtrip(Dict, Nothing, Dict, diagram) == diagram

# Round trip wiring diagrams with symbolic box and port values.

roundtrip_symbolic(f::WiringDiagram) = roundtrip(Symbol, Symbol, Nothing, f)

f = singleton_diagram(Box(:f, [:A], [:B]))
g = singleton_diagram(Box(:g, [:B], [:C]))

@test roundtrip_symbolic(f) == f
@test roundtrip_symbolic(compose(f,g)) == compose(f,g)
@test roundtrip_symbolic(otimes(f,g)) == otimes(f,g)

# Round trip nested, symbolic wiring diagrams.

inner = copy(f)
inner.value = :inner
outer = singleton_diagram(inner)
outer.value = :outer
@test roundtrip_symbolic(outer) == outer

end # module
