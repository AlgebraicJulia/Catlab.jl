module TestRelationalPrograms
using Test

using Catlab.CategoricalAlgebra.CSets
using Catlab.WiringDiagrams.UndirectedWiringDiagrams
using Catlab.Programs.RelationalPrograms

# Relations
###########

# Untyped relations

parsed = @relation (x,z) where (x,y,z) begin
  R(x,y)
  S(y,z)
end

d = RelationDiagram{Symbol}(2)
add_box!(d, 2, name=:R); add_box!(d, 2, name=:S)
add_junctions!(d, 3, variable=[:x,:y,:z])
set_junction!(d, [1,2,2,3])
set_junction!(d, [1,3], outer=true)
@test parsed == d

parsed = @relation ((x,z) where (x,y,z)) -> (R(x,y); S(y,z))
@test parsed == d

parsed = @relation function (x,z) where (x,y,z); R(x,y); S(y,z) end
@test parsed == d

# Typed relations

parsed = @relation (x,y,z) where (x::X, y::Y, z::Z, w::W) begin
  R(x,w)
  S(y,w)
  T(z,w)
end
d = RelationDiagram{Symbol}([:X,:Y,:Z])
add_box!(d, [:X,:W], name=:R)
add_box!(d, [:Y,:W], name=:S)
add_box!(d, [:Z,:W], name=:T)
add_junctions!(d, [:X,:Y,:Z,:W], variable=[:x,:y,:z,:w])
set_junction!(d, [1,4,2,4,3,4])
set_junction!(d, [1,2,3], outer=true)
@test parsed == d

# Tensor networks
#################

# Parsing
#--------

parsed = @tensor_network (i,j,k,ℓ) D[i,j,k] = A[i,ℓ] * B[j,ℓ] * C[k,ℓ]
d = RelationDiagram{Symbol}(3)
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
d = singleton_diagram(RelationDiagram{Symbol}, 3, name=:A)
set_subpart!(d, :variable, [:i,:j,:k])
@test parsed == d

# Degenerate case: no terms.
parsed = @tensor_network A[i,j] = 1
d = RelationDiagram{Symbol}(2)
add_junctions!(d, 2, variable=[:i,:j])
set_junction!(d, 1:2, outer=true)
@test parsed == d

# Round trip
#-----------

# Parse and then compile.
macro roundtrip_tensor(tensor)
  quote
    compiled = compile_tensor_expr(@tensor_network($tensor),
                                   assign_op=:(=), assign_name=:out)
    @test compiled == $(QuoteNode(tensor))
  end
end

@roundtrip_tensor out[i,k] = A[i,j] * B[j,k]
@roundtrip_tensor out[i,j,k] = A[i,ℓ] * B[j,ℓ] * C[k,ℓ]
@roundtrip_tensor out = u[i] * A[i,j] * v[j]
@roundtrip_tensor out[j] = α * a[i] * B[i,j]

end
