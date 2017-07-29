module TestWiring

using Catlab.Doctrine
using Catlab.Diagram.Wiring
using Base.Test

# Low-level graph interface
###########################

A, B, C, D = Ob(FreeSymmetricMonoidalCategory, :A, :B, :C, :D)
f = Hom(:f, A, B)
g = Hom(:g, B, C)

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
@test wire_type(d, Port(input_id(d),Output,1)) == A
@test wire_type(d, Port(output_id(d),Input,1)) == C
@test wire_type(d, Port(fv,Input,1)) == A
@test wire_type(d, Port(fv,Output,1)) == B
@test nwires(d) == 0
@test !has_wire(d, fv, gv)
@test !has_wire(d, (fv,1) => (gv,1))
add_wire!(d, (input_id(d),1) => (fv,1))
add_wire!(d, (fv,1) => (gv,1))
add_wire!(d, (gv,1) => (output_id(d),1))
@test nwires(d) == 3
@test has_wire(d, fv, gv)
@test has_wire(d, (fv,1) => (gv,1))
@test wire_type(d, (fv,1) => (gv,1)) == B
@test_throws WireTypeError add_wire!(d, (gv,1) => (fv,1))
@test wires(d) == map(Wire, [
  (input_id(d),1) => (fv,1),
  (fv,1) => (gv,1),
  (gv,1) => (output_id(d),1),
])
@test Set(all_neighbors(d, fv)) == Set([input_id(d),gv])
@test Set(all_neighbors(d, gv)) == Set([fv,output_id(d)])
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
f, g, h = Hom(:f,A,B), Hom(:g,B,C), Hom(:h,C,D)
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
f = WiringDiagram(Hom(:f,A,B))
g = WiringDiagram(Hom(:g,B,A))
@test nboxes(f) == 1
@test boxes(f) == [ HomBox(Hom(:f,A,B)) ]
@test nwires(f) == 2
@test WireTypes([A]) == WireTypes([A])
@test WiringDiagram(Hom(:f,A,B)) == WiringDiagram(Hom(:f,A,B))

# Composition
@test nboxes(compose(f,g)) == 2
@test boxes(compose(f,g)) == [ HomBox(Hom(:f,A,B)), HomBox(Hom(:g,B,A)) ]
@test nwires(compose(f,g)) == 3

# Domains and codomains
@test dom(f) == WireTypes([A])
@test codom(f) == WireTypes([B])
@test dom(compose(f,g)) == WireTypes([A])
@test codom(compose(f,g)) == WireTypes([A])
@test_throws Exception compose(f,f)

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

# Diagonals
#----------

# Basic composition
d = WiringDiagram(dom(f), otimes(codom(f),codom(f)))
fv1 = add_box!(d, first(boxes(f)))
fv2 = add_box!(d, first(boxes(f)))
add_wires!(d, [
  (input_id(d),1) => (fv1,1),
  (input_id(d),1) => (fv2,1),
  (fv1,1) => (output_id(d),1),
  (fv2,1) => (output_id(d),2),
])
@test compose(mcopy(dom(f)), otimes(f,f)) == d

# Domains and codomains
@test dom(mcopy(WireTypes([A]))) == WireTypes([A])
@test codom(mcopy(WireTypes([A]))) == WireTypes([A,A])
@test dom(mcopy(WireTypes([A,B]),3)) == WireTypes([A,B])
@test codom(mcopy(WireTypes([A,B]),3)) == WireTypes([A,B,A,B,A,B])

# Associativity
X = WireTypes([A])
@test compose(mcopy(X), otimes(id(X),mcopy(X))) == mcopy(X,3)
@test compose(mcopy(X), otimes(mcopy(X),id(X))) == mcopy(X,3)

# Commutativity
@test compose(mcopy(X), braid(X,X)) == mcopy(X)

# Unit
@test compose(mcopy(X), otimes(id(X),delete(X))) == id(X)

# Codiagonals
#------------

# Domains and codomains
@test dom(mmerge(WireTypes([A]))) == WireTypes([A,A])
@test codom(mmerge(WireTypes([A]))) == WireTypes([A])
@test dom(mmerge(WireTypes([A,B]),3)) == WireTypes([A,B,A,B,A,B])
@test codom(mmerge(WireTypes([A,B]),3)) == WireTypes([A,B])

# Associativity
X = WireTypes([A])
@test compose(otimes(id(X),mmerge(X)), mmerge(X)) == mmerge(X,3)
@test compose(otimes(mmerge(X),id(X)), mmerge(X)) == mmerge(X,3)

# Commutativity
@test compose(braid(X,X), mmerge(X)) == mmerge(X)

# Unit
@test compose(otimes(id(X),create(X)), mmerge(X)) == id(X)

# Expression conversion
#----------------------

# Functorality
f, g = Hom(:f,A,B), Hom(:g,B,A)
fd, gd = WiringDiagram(f), WiringDiagram(g)
@test to_wiring_diagram(f) == fd
@test to_wiring_diagram(compose(f,g)) == compose(fd,gd)
@test to_wiring_diagram(otimes(f,g)) == otimes(fd,gd)
@test to_wiring_diagram(munit(FreeSymmetricMonoidalCategory.Ob)) == munit(WireTypes)

end
