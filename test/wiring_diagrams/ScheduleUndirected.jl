module TestScheduleUndirectedWiringDiagrams
using Test

using LinearAlgebra: dot, tr

using Catlab.Theories: codom
using Catlab.CategoricalAlgebra.CSets
using Catlab.WiringDiagrams, Catlab.Programs.RelationalPrograms
using Catlab.WiringDiagrams.ScheduleUndirectedWiringDiagrams:
  composites, composite_junction, composite_ports, parent, box_parent

composite_junctions(x::AbstractACSet, c) =
  composite_junction.(Ref(x), composite_ports(x, c))

""" Generalized contraction of two tensors of arbitrary rank.

This function includes matrix multiplication, tensor product, and trace as
special cases.

FIXME: Put this somewhere else?
"""
function general_tensor_contract((A, B), (jA, jB), j_out)
  njunc = length(codom(j_out))
  jA, jB, j_out = Tuple(collect(jA)), Tuple(collect(jB)), Tuple(collect(j_out))
  jsizes = fill(-1, njunc)
  for (i,j) in enumerate(jA); jsizes[j] = size(A, i) end
  for (i,j) in enumerate(jB); jsizes[j] = size(B, i) end
  jsizes = Tuple(jsizes)

  C = zeros(eltype(A), Tuple(jsizes[j] for j in j_out))
  for index in CartesianIndices(jsizes)
    C[(index[j] for j in j_out)...] +=
      A[(index[j] for j in jA)...] * B[(index[j] for j in jB)...]
  end
  return C
end

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
out = eval_schedule(general_tensor_contract, nd, matrices)
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
out = eval_schedule(general_tensor_contract, nd, matrices)
@test out[] ≈ tr(foldl(*, matrices))

# Tensor product
################

d = @tensor_network out[w,x,y,z] = A[w,x] * B[y,z]
s = schedule(d)
@test parent(s) == [1]
@test box_parent(s) == [1,1]

A, B = randn((3,4)), randn((5,6))
out = eval_schedule(general_tensor_contract, s, [A, B])
@test out ≈ (reshape(A, (3,4,1,1)) .* reshape(B, (1,1,5,6)))

# Frobenius inner product
#########################

d = @tensor_network out[] = A[x,y] * B[x,y]
s = schedule(d)
@test parent(s) == [1]
@test box_parent(s) == [1,1]

A, B = randn((5,5)), randn((5,5))
out = eval_schedule(general_tensor_contract, s, [A, B])
@test out[] ≈ dot(vec(A), vec(B))

end
