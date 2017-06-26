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

# Operations on boxes
fv = add_box!(d, f)
@test nboxes(d) == 1
@test box(d, fv) == HomBox(f)
rem_box!(d, fv)
@test nboxes(d) == 0

fv = add_box!(d, f)
gv = add_box!(d, g)
@test nboxes(d) == 2
@test boxes(d) == [HomBox(f),HomBox(g)]

# Operations on wires
@test nwires(d) == 0
@test !has_wire(d, fv, gv)
add_wire!(d, (input_id(d),1) => (fv,1))
add_wire!(d, (fv,1) => (gv,1))
add_wire!(d, (gv,1) => (output_id(d),1))
@test nwires(d) == 3
@test has_wire(d, fv, gv)
@test wires(d) == map(Wire, [
  (input_id(d),1) => (fv,1),
  (fv,1) => (gv,1),
  (gv,1) => (output_id(d),1),
])
@test all_neighbors(d, fv) == [input_id(d),gv]
@test all_neighbors(d, gv) == [fv,output_id(d)]
@test neighbors(d, fv) == [gv]
@test out_neighbors(d, fv) == [gv]
@test in_neighbors(d, gv) == [fv]
@test out_wires(d, Port(fv,Output,1)) == [ Wire((fv,1) => (gv,1)) ]
@test in_wires(d, Port(gv,Input,1)) == [ Wire((fv,1) => (gv,1)) ]
rem_wires!(d, fv, gv)
@test nwires(d) == 2
@test !has_wire(d, fv, gv)
rem_wire!(d, (input_id(d),1) => (fv,1))
@test wires(d) == [ Wire((gv,1) => (output_id(d),1)) ]

# Substitution
f, g, h = hom(:f,A,B), hom(:g,B,C), hom(:h,C,D)
sub = WiringDiagram(B,D)
gv = add_box!(sub, g)
hv = add_box!(sub, h)
add_wires!(sub, Pair[
  (input_id(sub),1) => (gv,1),
  (gv,1) => (hv,1),
  (hv,1) => (output_id(sub),1),
])
d = WiringDiagram(A,D)
fv = add_box!(d, f)
subv = add_box!(d, sub)
add_wires!(d, Pair[
  (input_id(d),1) => (fv,1),
  (fv,1) => (subv,1),
  (subv,1) => (output_id(d),1),
])
@test boxes(d) == [ HomBox(f), sub ]
@test boxes(sub) == [ HomBox(g), HomBox(h) ]
substitute!(d, subv)
@test nboxes(d) == 3
@test Set(boxes(d)) == Set([ HomBox(f), HomBox(g), HomBox(h) ])
box_map = Dict(box(d,v).expr => v for v in box_ids(d))
@test nwires(d) == 4
@test Set(wires(d)) == Set(map(Wire, [
  (input_id(d),1) => (box_map[f],1),
  (box_map[f],1) => (box_map[g],1),
  (box_map[g],1) => (box_map[h],1),
  (box_map[h],1) => (output_id(d),1),
]))

# High-level categorical interface
##################################

# Category
#---------

# Generators
f = WiringDiagram(hom(:f,A,B))
g = WiringDiagram(hom(:g,B,A))
@test nboxes(f) == 1
@test boxes(f) == [ HomBox(hom(:f,A,B)) ]
@test nwires(f) == 2
@test WireTypes([A]) == WireTypes([A])
@test WiringDiagram(hom(:f,A,B)) == WiringDiagram(hom(:f,A,B))

# Composition
@test nboxes(compose(f,g)) == 2
@test boxes(compose(f,g)) == [ HomBox(hom(:f,A,B)), HomBox(hom(:g,B,A)) ]
@test nwires(compose(f,g)) == 3

# Domains and codomains
@test dom(f) == WireTypes([A])
@test codom(f) == WireTypes([B])
@test dom(compose(f,g)) == WireTypes([A])
@test codom(compose(f,g)) == WireTypes([A])

# Associativity
@test compose(compose(f,g),f) == compose(f,compose(g,f))

# Identity
@test compose(id(dom(f)), f) == f
@test compose(f, id(codom(f))) == f

# Symmetric monoidal category
#----------------------------

# Domains and codomains
@test dom(otimes(f,g)) == otimes(dom(f),dom(g))
@test codom(otimes(f,g)) == otimes(codom(f),codom(g))

# Associativity and unit
X, Y = WireTypes([A,B]), WireTypes([C,D])
I = munit(WireTypes)
@test otimes(X,I) == X
@test otimes(I,X) == X
@test otimes(otimes(X,Y),X) == otimes(X,otimes(Y,X))
@test otimes(otimes(f,g),f) == otimes(f,otimes(g,f))

# Braiding
@test compose(braid(X,Y),braid(Y,X)) == id(otimes(X,Y))

end
