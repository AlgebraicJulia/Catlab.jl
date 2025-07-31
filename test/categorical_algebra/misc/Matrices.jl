module TestMatrices

using Test
using SparseArrays
using GATlab
using Catlab.CategoricalAlgebra.Misc.Matrices

# Dense matrices
################

const IntMat = MatC{Int}()

A, B, C = [1 2 3; 4 5 6], [1 -1; -1 2], [0 1; 1 0]

@withmodel IntMat (dom, codom, ⋅, id, ⊕,⊗, swap, mcopy, pair, copair, plus, 
                  braid) begin
  @test dom(A) == 3
  @test codom(A) == 2
  @test A⋅B == B*A
  @test id(dom(A))⋅A == A
  @test A⋅id(codom(A)) == A
  @test A⊕(B⊕C) == (A⊕B)⊕C
  @test swap(dom(A),dom(B))⋅(B⊕A)⋅swap(codom(B),codom(A)) == A⊕B
  @test pair(B,C) == mcopy(dom(B))⋅(B⊕C)
  @test copair(A,B) == (A⊕B)⋅plus(codom(A))
  @test A⊗(B⊗C) == (A⊗B)⊗C
  @test braid(dom(A),dom(B))⋅(B⊗A)⋅braid(codom(B),codom(A)) == A⊗B
end



# Sparse matrices
#################

A, B, C = sparse(A), sparse(B), sparse(C)

const SparseIntMat = SparseMatrixCSC{Int,Int}

@withmodel IntMat (dom, codom, ⋅, ⊗, ⊕, id) begin
  @test dom(A) == 3
  @test codom(A) == 2
  @test A⋅B isa SparseIntMat
  @test A⊕B isa SparseIntMat
  @test A⊗B isa SparseIntMat
  @test A⋅B == B*A
  @test id(dom(A))⋅A == A
  @test A⋅id(codom(A)) == A
end 


end # module
