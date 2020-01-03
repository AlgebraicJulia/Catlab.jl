module TestWiringDiagramAlgorithms

using Test
using Catlab.WiringDiagrams

A, B, C, D = [ Ports([sym]) for sym in [:A, :B, :C, :D] ]
I = munit(Ports)
f = singleton_diagram(Box(:f, [:A], [:B]))
g = singleton_diagram(Box(:g, [:B], [:C]))
h = singleton_diagram(Box(:h, [:C], [:D]))

# Normalization
###############

# Normalize copies.
d = compose(mcopy(A), otimes(f,f))
normalized = compose(f, mcopy(B))
@test normalize_copy!(d) == normalized

d = compose(f, mcopy(B), otimes(g,g))
normalize_copy!(d)
normalized = compose(f, g, mcopy(C))
perm = sortperm(boxes(d); by=box->box.value)
@test is_permuted_equal(d, normalized, perm)

d = compose(mcopy(A), otimes(f,f), otimes(g,g))
normalize_copy!(d)
perm = sortperm(boxes(d); by=box->box.value)
@test is_permuted_equal(d, normalized, perm)

# Normalize deletions.
@test normalize_delete!(copy(f)) == f

d = WiringDiagram(I,I)
add_box!(d, first(boxes(f)))
@test normalize_delete!(d) == WiringDiagram(I,I)

d = WiringDiagram(A, B)
fv = add_box!(d, first(boxes(f)))
gv = add_box!(d, first(boxes(g)))
hv = add_box!(d, first(boxes(h)))
add_wires!(d, [
  (input_id(d),1) => (fv,1),
  (fv,1) => (gv,1),
  (gv,1) => (hv,1),
  (fv,1) => (output_id(d),1),
])
@test normalize_delete!(d) == f

# Normalize wiring diagrams representing morphisms in a cartesian category.
d = compose(
  mcopy(A),
  otimes(id(A),mcopy(A)),
  otimes(f,f,f),
  otimes(id(B), id(B), compose(g, delete(C)))
)
normalized = compose(f, mcopy(B))
@test normalize_cartesian!(d) == normalized

# Layout
########

@test crossing_minimization_by_sort(f, box_ids(f), sources=[input_id(d)]) == [1]

d = otimes(f,g)
@test crossing_minimization_by_sort(d, box_ids(d), sources=[input_id(d)]) == [1,2]

d = WiringDiagram(I,I)
fv1, fv2 = add_box!(d, first(boxes(f))), add_box!(d, first(boxes(f)))
gv1, gv2 = add_box!(d, first(boxes(g))), add_box!(d, first(boxes(g)))
add_wires!(d, [ Wire((fv1,1) => (gv1,1)), Wire((fv2,1),(gv2,1)) ])
@test crossing_minimization_by_sort(d, [gv1,gv2], sources=[fv1,fv2]) == [1,2]
@test crossing_minimization_by_sort(d, [fv1,fv2], targets=[gv1,gv2]) == [1,2]

end
