module TestGraphML

using Base.Test
using LightXML
using Catlab.Doctrine
using Catlab.Diagram

function roundtrip(f::WiringDiagram)
  xdoc = write_graphml(Symbol, Void, Symbol, f)
  read_graphml(Symbol, Void, Symbol, xdoc)
end

A, B, C = Ob(FreeSymmetricMonoidalCategory, :A, :B, :C)
f = WiringDiagram(Hom(:f, A, B))
g = WiringDiagram(Hom(:g, B, C))

@test roundtrip(f) == f
@test roundtrip(compose(f,g)) == compose(f,g)
@test roundtrip(otimes(f,g)) == otimes(f,g)

end
