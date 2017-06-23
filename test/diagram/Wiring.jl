module TestWiring

using Catlab.Doctrine
using Catlab.Diagram.Wiring
using Base.Test

# Low-level graph interface
###########################

A,B,C,D = [ ob(FreeSymmetricMonoidalCategory, sym) for sym in [:A,:B,:C,:D] ]
f = hom(:f, A, B)
g = hom(:g, B, C)

diagram = WiringDiagram(A, C)
@test has_node(diagram, diagram)

f_node = add_node!(diagram, f)
@test has_node(diagram, f_node)
rem_node!(diagram, f_node)
@test !has_node(diagram, f_node)

end
