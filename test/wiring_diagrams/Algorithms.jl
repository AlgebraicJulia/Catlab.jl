module TestWiringDiagramAlgorithms

using Test
using Catlab.Doctrines
using Catlab.WiringDiagrams

A, B, C, D = Ob(FreeBiproductCategory, :A, :B, :C, :D)
I = munit(FreeBiproductCategory.Ob)
f = Hom(:f, A, B)
g = Hom(:g, B, C)
h = Hom(:h, C, D)

# Diagonals and codiagonals
###########################

junction_diagram(args...) = singleton_diagram(Junction(args...))

# Add junctions for copies.
d = to_wiring_diagram(compose(f, mcopy(B)))
original = copy(d)
junctioned = compose(to_wiring_diagram(f), junction_diagram(:B,1,2))
@test add_junctions!(d) == junctioned
@test remove_junctions!(d) == original

# Add junctions for merges.
d = to_wiring_diagram(compose(mmerge(A), f))
original = copy(d)
junctioned = compose(junction_diagram(:A,2,1), to_wiring_diagram(f))
@test is_permuted_equal(add_junctions!(d), junctioned, [2,1])
@test remove_junctions!(d) == original

# Add junctions for deletions.
d = to_wiring_diagram(compose(f, delete(B)))
original = copy(d)
junctioned = compose(to_wiring_diagram(f), junction_diagram(:B,1,0))
@test add_junctions!(d) == junctioned
@test remove_junctions!(d) == original

# Add junctions for creations.
d = to_wiring_diagram(compose(create(A), f))
original = copy(d)
junctioned = compose(junction_diagram(:A,0,1), to_wiring_diagram(f))
@test is_permuted_equal(add_junctions!(d), junctioned, [2,1])
@test remove_junctions!(d) == original

# Add junctions for copies, merges, deletions, and creations, all at once.
d = to_wiring_diagram(compose(create(A),f,mcopy(B),mmerge(B),g,delete(C)))
original = copy(d)
junctioned = compose(
  junction_diagram(:A,0,1),
  to_wiring_diagram(f),
  junction_diagram(:B,1,2),
  junction_diagram(:B,2,1),
  to_wiring_diagram(g),
  junction_diagram(:C,1,0)
)
d = add_junctions!(d)
# XXX: An isomorphism test would be more convenient.
perm = [ findfirst([b] .== boxes(d)) for b in boxes(junctioned) ]
@test is_permuted_equal(d, junctioned, perm)
@test remove_junctions!(d) == original

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
@test crossing_minimization_by_sort(d, [input_id(d)], box_ids(d)) == [1]

d = to_wiring_diagram(otimes(f,g))
@test crossing_minimization_by_sort(d, [input_id(d)], box_ids(d)) == [1,2]

d = WiringDiagram(I,I)
fv1, fv2 = add_box!(d, f), add_box!(d, f)
gv1, gv2 = add_box!(d, g), add_box!(d, g)
add_wires!(d, [ Wire((fv1,1) => (gv1,1)), Wire((fv2,1),(gv2,1)) ])
@test crossing_minimization_by_sort(d, [fv1,fv2], [gv1,gv2]) == [1,2]

end
