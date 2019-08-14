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
d = to_wiring_diagram(compose(mcopy(A), otimes(f,f)))
normal = to_wiring_diagram(compose(f, mcopy(B)))
@test normalize_copy!(d) == normal

d = to_wiring_diagram(compose(f, mcopy(B), otimes(g,g)))
normalize_copy!(d)
normal = to_wiring_diagram(compose(f, g, mcopy(C)))
perm = sortperm(boxes(d); by=box->box.value)
@test is_permuted_equal(d, normal, perm)

d = to_wiring_diagram(compose(mcopy(A), otimes(f,f), otimes(g,g)))
normalize_copy!(d)
perm = sortperm(boxes(d); by=box->box.value)
@test is_permuted_equal(d, normal, perm)

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
d = to_wiring_diagram(compose(
  mcopy(A),
  otimes(id(A),mcopy(A)),
  otimes(f,f,f),
  otimes(id(B), id(B), compose(g, delete(C)))
))
normal = to_wiring_diagram(compose(f, mcopy(B)))
@test normalize_cartesian!(d) == normal

end
