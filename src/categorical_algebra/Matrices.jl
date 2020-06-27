""" Categories of matrices.
"""
module Matrices
export MatrixDom, dom, codom, id, compose, ⋅, ∘,
  otimes, ⊗, munit, braid, oplus, ⊕, mzero, swap,
  mcopy, Δ, delete, ◊, plus, zero, pair, copair, proj1, proj2, coproj1, coproj2

import Base: +, *, zero, one
using LinearAlgebra: I
using SparseArrays
import SparseArrays: blockdiag

using ...GAT
using ...Theories: DistributiveSemiadditiveCategory
import ...Theories: dom, codom, id, compose, ⋅, ∘,
  otimes, ⊗, munit, braid, oplus, ⊕, mzero, swap,
  mcopy, Δ, delete, ◊, plus, zero, pair, copair, proj1, proj2, coproj1, coproj2

# Matrices over a commutative rig
#################################

""" Domain or codomain of a Julia matrix of a specific type.

Object in the category of matrices of this type.
"""
struct MatrixDom{M <: AbstractMatrix}
  dim::Int
end

+(m::MD, n::MD) where MD <: MatrixDom = MD(m.dim + n.dim)
*(m::MD, n::MD) where MD <: MatrixDom = MD(m.dim * n.dim)
zero(::Type{MD}) where MD <: MatrixDom = MD(0)
one(::Type{MD}) where MD <: MatrixDom = MD(1)

""" Biproduct category of Julia matrices of specific type.

The matrices can be dense or sparse, and the element type can be any
[commutative rig](https://ncatlab.org/nlab/show/rig) (commutative semiring): any
Julia type implementing `+`, `*`, `zero`, `one` and obeying the axioms. Note
that commutativity is required only in order to define `braid`.

For a similar design (only for sparse matrices) by the Julia core developers,
see [SemiringAlgebra.jl](https://github.com/JuliaComputing/SemiringAlgebra.jl)
and [accompanying short paper](https://doi.org/10.1109/HPEC.2013.6670347).
"""
@instance DistributiveSemiadditiveCategory(MatrixDom, AbstractMatrix) begin
  # FIXME: Cannot define type-parameterized instances.
  #@instance AdditiveBiproductCategory(MatrixDom{M}, M) where M <: AbstractMatrix begin
  @import +, dom, codom, id, mzero, munit, braid
  
  compose(A::AbstractMatrix, B::AbstractMatrix) = B*A
  plus(A::AbstractMatrix, B::AbstractMatrix) = A+B
  
  oplus(m::MatrixDom, n::MatrixDom) = m+n
  oplus(A::AbstractMatrix, B::AbstractMatrix) = blockdiag(A, B)
  swap(m::MatrixDom, n::MatrixDom) = [zero(n,m) id(n); id(m) zero(m,n)]
  
  otimes(m::MatrixDom, n::MatrixDom) = m*n
  otimes(A::AbstractMatrix, B::AbstractMatrix) = kron(A, B)
  
  mcopy(m::MatrixDom) = pair(id(m), id(m))
  delete(m::MatrixDom) = zero(zero(typeof(m)), m)
  plus(m::MatrixDom) = copair(id(m), id(m))
  zero(m::MatrixDom) = zero(m, zero(typeof(m)))
  
  pair(A::AbstractMatrix, B::AbstractMatrix) = [A; B]
  copair(A::AbstractMatrix, B::AbstractMatrix) = [A B]
  proj1(m::MatrixDom, n::MatrixDom) = [id(m) zero(m,n)]
  proj2(m::MatrixDom, n::MatrixDom) = [zero(n,m) id(n)]
  coproj1(m::MatrixDom, n::MatrixDom) = [id(m); zero(n,m)]
  coproj2(m::MatrixDom, n::MatrixDom) = [zero(m,n); id(n)]
end

dom(A::M) where M <: AbstractMatrix = MatrixDom{M}(size(A,2))
codom(A::M) where M <: AbstractMatrix = MatrixDom{M}(size(A,1))

id(m::MatrixDom{M}) where M = M(I, m.dim, m.dim)
mzero(::Type{MD}) where MD <: MatrixDom = MD(0)
munit(::Type{MD}) where MD <: MatrixDom = MD(1)
braid(m::MatrixDom{M}, n::MatrixDom{M}) where M =
  vec_permutation_matrix(M, m.dim, n.dim)
zero(m::MatrixDom{M}, n::MatrixDom{M}) where M = zero_matrix(M, m.dim, n.dim)

# Matrix utilities
##################

# Block diagonal only implemented for sparse matrices.
blockdiag(A::AbstractMatrix...) = cat(A..., dims=(1,2))

# Dense and sparse matrices have different APIs for creating zero matrices.
zero_matrix(::Type{Matrix{T}}, dims...) where T = zeros(T, dims...)
zero_matrix(::Type{SparseMatrixCSC{T}}, dims...) where T = spzeros(T, dims...)

function unit_vector(::Type{M}, n::Int, i::Int) where {T, M <: AbstractMatrix{T}}
  x = zero_matrix(M, n, 1)
  x[i,1] = one(T)
  x
end

""" The "vec-permutation" matrix, aka the "perfect shuffle" permutation matrix.

This formula is (Henderson & Searle, 1981, "The vec-permutation matrix, the vec
operator and Kronecker products: a review", Equation 18). Many other formulas
are given there.
"""
function vec_permutation_matrix(::Type{M}, m::Int, n::Int) where M <: AbstractMatrix
  hcat((kron(M(I, n, n), unit_vector(M, m, j)) for j in 1:m)...)
end

end
