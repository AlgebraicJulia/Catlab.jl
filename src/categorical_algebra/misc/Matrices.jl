""" Categories of matrices.
"""
module Matrices
export MatC, dom, codom, id, compose, ⋅, ∘,
  otimes, ⊗, munit, braid, oplus, ⊕, mzero, swap,
  mcopy, Δ, delete, ◊, plus, zero, pair, copair, proj1, proj2, coproj1, coproj2

import Base: +, *, zero, one
using LinearAlgebra: I
using SparseArrays
import SparseArrays: blockdiag

using GATlab
using ....Theories: ThDistributiveSemiadditiveCategory
import ....Theories: dom, codom, id, compose, ⋅, ∘,
  otimes, ⊗, munit, braid, oplus, ⊕, mzero, swap,
  mcopy, Δ, delete, ◊, plus, zero, pair, copair, proj1, proj2, coproj1, coproj2

# Matrices over a commutative rig
#################################

struct MatC{T <: Number} end

@instance ThDistributiveSemiadditiveCategory{Int, AbstractMatrix{T}} [model::MatC{T}] where {T} begin
  Ob(n::Int) = n >= 0 ? n : error("expected nonnegative integer")
  Hom(A::AbstractMatrix{T}, n::Int, m::Int) =
    size(A) == (n,m) ? A : error("expected dimensions to be $((n,m))")

  id(n::Int)::AbstractMatrix{T} = T[T(i == j) for i in 1:n, j in 1:n]
  compose(A::AbstractMatrix{T}, B::AbstractMatrix{T}) = B * A

  dom(A::AbstractMatrix{T})::Int = size(A,2)
  codom(A::AbstractMatrix{T})::Int = size(A,1)

  oplus(m::Int, n::Int)::Int = m+n
  otimes(m::Int, n::Int)::Int = m*n

  oplus(A::AbstractMatrix{T}, B::AbstractMatrix{T}) = blockdiag(A, B)
  otimes(A::AbstractMatrix{T}, B::AbstractMatrix{T}) = kron(A, B)

  mzero()::Int = 0
  munit()::Int = 1

  swap(m::Int, n::Int) = 
    [zeros(T, (n,m)) id[model](n); id[model](m) zeros(T, (m,n))]

  braid(m::Int, n::Int) =
    hcat((kron(id[model](n), unit_vector(T, m, j)) for j in 1:m)...)

  zero(m::Int) = zeros(T, (m, m))

  plus(m::Int)::AbstractMatrix{T} = copair[model](id[model](m), id[model](m))
  plus(A::AbstractMatrix{T}, B::AbstractMatrix{T}) = A+B

  copair(A::AbstractMatrix{T}, B::AbstractMatrix{T}) = [A B]
  proj1(m::Int, n::Int) = [id(m) zeros(T, (m,n))]
  proj2(m::Int, n::Int) = [zeros(T, (n,m)) id(n)]
  coproj1(m::Int, n::Int) = [id(m); zeros(T, (n,m))]
  coproj2(m::Int, n::Int) = [zeros(T, (m,n)); id(n)]

  pair(A::AbstractMatrix{T}, B::AbstractMatrix{T}) = [A; B]
  mcopy(m::Int) = pair[model](id[model](m), id[model](m))

end

# Utilities
###########

blockdiag(A::AbstractMatrix...) = cat(A..., dims=(1,2))

""" E.g. `unit_vector(Int, 6, 5) == [0 0 0 0 1 0]` Returns a spare matrix"""
function unit_vector(::Type{T}, n::Int, i::Int) where {T}
  x = spzeros(T, n, 1)
  x[i,1] = one(T)
  x
end

zero_matrix(::Type{Matrix{T}}, dims...) where T = zeros(T, dims...)

zero_matrix(::Type{SparseMatrixCSC{T}}, dims...) where T = spzeros(T, dims...)


end # module
