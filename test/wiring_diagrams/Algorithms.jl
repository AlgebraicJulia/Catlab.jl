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

# Layout
########

d = to_wiring_diagram(f)
@test crossing_minimization_by_sort(d, [input_id(d)], box_ids(d)) == [1]

d = to_wiring_diagram(otimes(f,g))
@test crossing_minimization_by_sort(d, [input_id(d)], box_ids(d)) == [1,2]

d = WiringDiagram(I,I)
fv1, fv2 = add_box!(d, f), add_box!(d, f)
gv1, gv2 = add_box!(d, g), add_box!(d, g)
add_wires!(d, [ Wire((fv1,1) => (gv1,1)), Wire((fv2,1),(gv2,1)) ])
@test crossing_minimization_by_sort(d, [fv1,fv2], [gv1,gv2]) == [1,2]

end
