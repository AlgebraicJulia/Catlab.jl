module TestWiringDiagramAlgorithms

using Test
using Catlab.Doctrines
using Catlab.WiringDiagrams

A, B, C, D = Ob(FreeCartesianCategory, :A, :B, :C, :D)
I = munit(FreeCartesianCategory.Ob)
f = Hom(:f, A, B)
g = Hom(:g, B, C)
h = Hom(:h, C, D)

# Normal forms
##############

# Copies.
original = compose(mcopy(A), otimes(f,f))
normal = compose(f, mcopy(B))
@test normalize_copy!(to_wiring_diagram(original)) == to_wiring_diagram(normal)

original = compose(f, mcopy(B), otimes(g,g))
# XXX: Need wiring diagram isomorphism.
#normal = compose(f, g, mcopy(C))
#@test normalize_copy!(to_wiring_diagram(original)) == to_wiring_diagram(normal)
normal = WiringDiagram(A, otimes(C,C))
gv = add_box!(normal, g)
fv = add_box!(normal, f)
add_wires!(normal, Pair[
  (input_id(normal),1) => (fv,1),
  (fv,1) => (gv,1),
  (gv,1) => (output_id(normal),1),
  (gv,1) => (output_id(normal),2),
])
@test normalize_copy!(to_wiring_diagram(original)) == normal

original = compose(mcopy(A), otimes(f,f), otimes(g,g))
#normal = compose(f, g, mcopy(C))
#@test normalize_copy!(to_wiring_diagram(original)) == to_wiring_diagram(normal)
@test normalize_copy!(to_wiring_diagram(original)) == normal

# Deletions.
d = WiringDiagram(f)
@test normalize_delete!(d) == d

d = WiringDiagram(I,I)
add_box!(d, f)
@test normalize_delete!(d) == WiringDiagram(I,I)

d = WiringDiagram(A, B)
fv = add_box!(d, f)
gv = add_box!(d, g)
hv = add_box!(d, h)
add_wires!(d, [
  (input_id(d),1) => (fv,1),
  (fv,1) => (gv,1),
  (gv,1) => (hv,1),
  (fv,1) => (output_id(d),1),
])
@test normalize_delete!(d) == WiringDiagram(f)

# Cartesian morphisms.
original = compose(
  mcopy(A),
  otimes(id(A),mcopy(A)),
  otimes(f,f,f),
  otimes(id(B), id(B), compose(g, delete(C)))
)
normal = compose(f, mcopy(B))
@test normalize_cartesian!(to_wiring_diagram(original)) == 
  to_wiring_diagram(normal)

end
