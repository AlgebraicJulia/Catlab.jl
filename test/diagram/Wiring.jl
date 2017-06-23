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
@test nboxes(diagram) == 1
@test box(diagram,1) == diagram

fv = add_box!(diagram, f)
@test nboxes(diagram) == 2
@test box(diagram, 2) == HomBox(f)

rem_box!(diagram, 2)
@test nboxes(diagram) == 1

end
