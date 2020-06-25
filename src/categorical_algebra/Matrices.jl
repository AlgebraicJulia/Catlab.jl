""" Categories of matrices.
"""
module Matrices
export MatrixDom, dom, codom, id, compose, ⋅, ∘, oplus, ⊕, mzero, braid, σ,
  mcopy, Δ, delete, ◊, plus, zero, pair, copair, proj1, proj2, coproj1, coproj2

import Base: +, *, zero, one
using LinearAlgebra: I
using SparseArrays
import SparseArrays: blockdiag

using ...GAT
using ...Theories: AdditiveBiproductCategory
import ...Theories: dom, codom, id, compose, ⋅, ∘, oplus, ⊕, mzero, braid, σ,
  mcopy, Δ, delete, ◊, plus, zero, pair, copair, proj1, proj2, coproj1, coproj2


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
[rig](https://ncatlab.org/nlab/show/rig) (semiring): any Julia type implementing
`+`, `*`, `zero`, `one` and obeying the rig axioms.

For a similar design (only for sparse matrices) by the Julia core developers,
see [SemiringAlgebra.jl](https://github.com/JuliaComputing/SemiringAlgebra.jl)
and [accompanying short paper](https://doi.org/10.1109/HPEC.2013.6670347).
"""
@instance AdditiveBiproductCategory(MatrixDom, AbstractMatrix) begin
  # FIXME: Cannot define type-parameterized instances.
  #@instance AdditiveBiproductCategory(MatrixDom{M}, M) where M <: AbstractMatrix begin
  @import dom, codom, id, mzero
  
  plus(A::AbstractMatrix, B::AbstractMatrix) = A+B
  compose(A::AbstractMatrix, B::AbstractMatrix) = B*A
  oplus(m::MatrixDom, n::MatrixDom) = m+n
  oplus(A::AbstractMatrix, B::AbstractMatrix) = blockdiag(A, B)
  braid(m::MatrixDom, n::MatrixDom) = [zero(n,m) id(n); id(m) zero(m,n)]
  
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
zero(m::MatrixDom{M}, n::MatrixDom{M}) where M = zero_matrix(M, m.dim, n.dim)

# Block diagonal only implemented for sparse matrices.
blockdiag(A::AbstractMatrix...) = cat(A..., dims=(1,2))

# Dense and sparse matrices have different APIs for creating zero matrices.
zero_matrix(::Type{<:AbstractMatrix{T}}, dims...) where T = zeros(T, dims...)
zero_matrix(::Type{SparseMatrixCSC{T}}, dims...) where T = spzeros(T, dims...)

end
