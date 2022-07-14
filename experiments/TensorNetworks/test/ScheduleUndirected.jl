module TestScheduleUndirectedWiringDiagrams
using Test

using LinearAlgebra: dot, tr

using Catlab.Theories: codom
using Catlab.CategoricalAlgebra.CSets
using Catlab.WiringDiagrams
using Catlab.WiringDiagrams.ScheduleUndirectedWiringDiagrams:
  composites, composite_junction, composite_ports, parent, box_parent
using TensorNetworks.TensorNetworks: @tensor_network

composite_junctions(x::ACSet, c) =
  composite_junction.(Ref(x), composite_ports(x, c))

# Open linear path
##################

d = @tensor_network out[v,z] = A[v,w] * B[w,x] * C[x,y] * D[y,z]
s = schedule(d, order=reverse(boxes(d)))
@test length(composites(s)) == 3
@test parent(s) == [2,3,3]
@test box_parent(s) == [3,2,1,1]

nd = to_nested_diagram(s)
@test parent(nd) == [2,3,3]
@test box_parent(nd) == [3,2,1,1]
@test composite_junctions(nd, 1:3) == [[3,5], [2,5], [1,5]]

matrices = map(randn, [(3,4), (4,5), (5,6), (6,7)])
out = eval_schedule(nd, matrices)
@test out ≈ foldr(*, matrices)

# Closed cycle
##############

d = @tensor_network out[] = A[w,x] * B[x,y] * C[y,z] * D[z,w]
s = schedule(d)
nd = to_nested_diagram(s)
@test parent(nd) == [2,3,3]
@test box_parent(nd) == [1,1,2,3]
@test map(length, composite_ports(nd, 1:3)) == [2,2,0]
@test composite_junctions(nd, 1:2) == [[1,3], [1,4]]

matrices = map(randn, [(10,5), (5,5), (5,5), (5,10)])
out = eval_schedule(nd, matrices)
@test out[] ≈ tr(foldl(*, matrices))

# Tensor product
################

d = @tensor_network out[w,x,y,z] = A[w,x] * B[y,z]
s = schedule(d)
@test parent(s) == [1]
@test box_parent(s) == [1,1]

A, B = randn((3,4)), randn((5,6))
out = eval_schedule(s, [A, B])
@test out ≈ (reshape(A, (3,4,1,1)) .* reshape(B, (1,1,5,6)))

# Frobenius inner product
#########################

d = @tensor_network out[] = A[x,y] * B[x,y]
s = schedule(d)
@test parent(s) == [1]
@test box_parent(s) == [1,1]

A, B = randn((5,5)), randn((5,5))
out = eval_schedule(s, [A, B])
@test out[] ≈ dot(vec(A), vec(B))

end
