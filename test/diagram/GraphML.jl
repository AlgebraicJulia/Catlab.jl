module TestGraphML

using Base.Test
using LightXML
using Catlab.Doctrine
using Catlab.Diagram

to_gml(f::WiringDiagram) = to_graphml(Symbol, Void, Symbol, f)

A, B, C = Ob(FreeSymmetricMonoidalCategory, :A, :B, :C)
f = WiringDiagram(Hom(:f, A, B))
g = WiringDiagram(Hom(:g, B, C))

@test isa(to_gml(f), XMLDocument)
@test isa(to_gml(compose(f,g)), XMLDocument)
@test isa(to_gml(otimes(f,g)), XMLDocument)

end
