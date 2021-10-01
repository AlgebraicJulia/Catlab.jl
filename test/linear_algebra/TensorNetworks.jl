module TestTensorNetworks
using Test

using LinearAlgebra: tr

using Catlab.CategoricalAlgebra.CSets, Catlab.WiringDiagrams
using Catlab.LinearAlgebra.TensorNetworks

# Parsing and code generation
#############################

# Parsing
#--------

parsed = @tensor_network (i,j,k,ℓ) D[i,j,k] = A[i,ℓ] * B[j,ℓ] * C[k,ℓ]
d = RelationDiagram(3)
add_box!(d, 2, name=:A); add_box!(d, 2, name=:B); add_box!(d, 2, name=:C)
add_junctions!(d, 4, variable=[:i,:j,:k,:ℓ])
set_junction!(d, [1,4,2,4,3,4])
set_junction!(d, 1:3, outer=true)
@test parsed == d

parsed = @tensor_network D[i,j,k] = A[i,ℓ] * B[j,ℓ] * C[k,ℓ]
@test parsed == d
parsed = @tensor_network D[i,j,k] := A[i,ℓ] * B[j,ℓ] * C[k,ℓ]
@test parsed == d

# Degenerate case: single term.
parsed = @tensor_network B[i,j,k] = A[i,j,k]
d = singleton_diagram(RelationDiagram, 3, name=:A)
set_subpart!(d, :variable, [:i,:j,:k])
@test parsed == d

# Degenerate case: no terms.
parsed = @tensor_network A[i,j] = 1
d = RelationDiagram(2)
add_junctions!(d, 2, variable=[:i,:j])
set_junction!(d, 1:2, outer=true)
@test parsed == d

# Round trip: parse then compile
#-------------------------------

macro roundtrip_tensor(tensor)
  quote
    compiled = gen_tensor_notation(@tensor_network($tensor),
                                   assign_op=:(=), assign_name=:out)
    @test compiled == $(QuoteNode(tensor))
  end
end

@roundtrip_tensor out[i,k] = A[i,j] * B[j,k]
@roundtrip_tensor out[i,j,k] = A[i,ℓ] * B[j,ℓ] * C[k,ℓ]
@roundtrip_tensor out = u[i] * A[i,j] * v[j]
@roundtrip_tensor out[j] = α * a[i] * B[i,j]

# Evaluation
############

# Binary matrix multiply.
A, B = randn((3,4)), randn((4,5))
network = @tensor_network C[i,k] = A[i,j] * B[j,k]
@test oapply(network, [A,B]) ≈ A*B

# Ternary matrix multiply.
C = randn((5,6))
network = @tensor_network D[i,ℓ] = A[i,j] * B[j,k] * C[k,ℓ]
@test oapply(network, [A,B,C]) ≈ A*B*C

# Trace.
A = randn((5,5))
network = @tensor_network out[] = A[i,i]
@test oapply(network, [A])[] ≈ tr(A)

# Tensor product.
A, B = randn((3,4)), randn((5,6))
network = @tensor_network C[i,j,k,ℓ] = A[i,j] * B[k,ℓ]
@test oapply(network, [A,B]) ≈ (reshape(A, (3,4,1,1)) .* reshape(B, (1,1,5,6)))

end
