module TestWiring

using Catlab.Doctrine
using Catlab.Diagram.Wiring
using Base.Test

# Low-level graph interface
###########################

A,B,C,D = [ ob(FreeSymmetricMonoidalCategory, sym) for sym in [:A,:B,:C,:D] ]
f = hom(:f, A, B)
g = hom(:g, B, C)

d = WiringDiagram(A, C)
@test nboxes(d) == 0
@test box(d,input_id(d)) == d
@test box(d,output_id(d)) == d

# Mutations on boxes
fv = add_box!(d, f)
@test nboxes(d) == 1
@test box(d, fv) == HomBox(f)
rem_box!(d, fv)
@test nboxes(d) == 0

fv = add_box!(d, f)
gv = add_box!(d, g)
@test nboxes(d) == 2
@test boxes(d) == [HomBox(f),HomBox(g)]

# Mutations on wires
@test nwires(d) == 0
@test !has_wire(d, fv, gv)
add_wire!(d, (input_id(d),1) => (fv,1))
add_wire!(d, (fv,1) => (gv,1))
add_wire!(d, (gv,1) => (output_id(d),1))
@test nwires(d) == 3
@test has_wire(d, fv, gv)
@test all_neighbors(d, fv) == [input_id(d),gv]
@test all_neighbors(d, gv) == [fv,output_id(d)]
@test neighbors(d, fv) == [gv]
@test out_neighbors(d, fv) == [gv]
@test in_neighbors(d, gv) == [fv]
rem_wires!(d, fv, gv)
@test nwires(d) == 2
@test !has_wire(d, fv, gv)

# Substitution
# TODO

end
