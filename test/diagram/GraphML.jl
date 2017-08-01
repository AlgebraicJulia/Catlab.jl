module TestGraphML

using Base.Test
using LightXML
using Catlab.Doctrine
using Catlab.Diagram

A, B, C = Ob(FreeSymmetricMonoidalCategory, :A, :B, :C)
f = WiringDiagram(Hom(:f, A, B))
g = WiringDiagram(Hom(:g, B, C))

@test isa(to_graphml(f), XMLDocument)
@test isa(to_graphml(compose(f,g)), XMLDocument)
@test isa(to_graphml(otimes(f,g)), XMLDocument)

end
