module TestWiringDiagramAlgorithms

using Test
using Catlab.Doctrines, Catlab.WiringDiagrams

# Normalization
###############

A, B, C, D = Ob(FreeCartesianCategory, :A, :B, :C, :D)
I = munit(FreeCartesianCategory.Ob)
f = Hom(:f, A, B)
g = Hom(:g, B, C)
h = Hom(:h, C, D)

# Normalize copies.
d = to_wiring_diagram(compose(mcopy(A), otimes(f,f)))
normalized = to_wiring_diagram(compose(f, mcopy(B)))
@test normalize_copy!(d) == normalized

d = to_wiring_diagram(compose(f, mcopy(B), otimes(g,g)))
normalize_copy!(d)
normalized = to_wiring_diagram(compose(f, g, mcopy(C)))
perm = sortperm(boxes(d); by=box->box.value)
@test is_permuted_equal(d, normalized, perm)

d = to_wiring_diagram(compose(mcopy(A), otimes(f,f), otimes(g,g)))
normalize_copy!(d)
perm = sortperm(boxes(d); by=box->box.value)
@test is_permuted_equal(d, normalized, perm)

# Normalize deletions.
d = to_wiring_diagram(f)
@test normalize_delete!(d) == to_wiring_diagram(f)

d = WiringDiagram(I,I)
add_box!(d, Box(f))
@test normalize_delete!(d) == WiringDiagram(I,I)

d = WiringDiagram(A, B)
fv = add_box!(d, Box(f))
gv = add_box!(d, Box(g))
hv = add_box!(d, Box(h))
add_wires!(d, [
  (input_id(d),1) => (fv,1),
  (fv,1) => (gv,1),
  (gv,1) => (hv,1),
  (fv,1) => (output_id(d),1),
])
@test normalize_delete!(d) == to_wiring_diagram(f)

# Normalize wiring diagrams representing morphisms in a cartesian category.
d = to_wiring_diagram(compose(
  mcopy(A),
  otimes(id(A),mcopy(A)),
  otimes(f,f,f),
  otimes(id(B), id(B), compose(g, delete(C)))
))
normalized = to_wiring_diagram(compose(f, mcopy(B)))
@test normalize_cartesian!(d) == normalized

# Layout
########

d = to_wiring_diagram(f)
@test crossing_minimization_by_sort(d, box_ids(d), sources=[input_id(d)]) == [1]

d = to_wiring_diagram(otimes(f,g))
@test crossing_minimization_by_sort(d, box_ids(d), sources=[input_id(d)]) == [1,2]

d = WiringDiagram(I,I)
fv1, fv2 = add_box!(d, Box(f)), add_box!(d, Box(f))
gv1, gv2 = add_box!(d, Box(g)), add_box!(d, Box(g))
add_wires!(d, [ Wire((fv1,1) => (gv1,1)), Wire((fv2,1),(gv2,1)) ])
@test crossing_minimization_by_sort(d, [gv1,gv2], sources=[fv1,fv2]) == [1,2]
@test crossing_minimization_by_sort(d, [fv1,fv2], targets=[gv1,gv2]) == [1,2]

end
