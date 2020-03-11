module StructuredGraphicalLinearAlgebra
export StructuredLinearFunctions, FreeStructuredLinearFunctions,
  Ob, Hom, dom, codom, compose, ⋅, ∘, id, oplus, ⊕, mzero, braid,
  mcopy, Δ, delete, ◊, plus, zero, plus, +, scalar, antipode, adjoint,
  ℝ, munit, →, diag

import Base: +
import LinearAlgebra: adjoint, diag

using ...Catlab, ...Doctrines
import ...Doctrines:
  Ob, Hom, dom, codom, compose, ⋅, ∘, id, oplus, ⊕, mzero, braid, munit
using ..GraphicalLinearAlgebra
import ..GraphicalLinearAlgebra:
  mcopy, Δ, delete, ◊, plus, zero, plus, +, scalar, antipode, adjoint

# Doctrines
###########

""" Doctrine of *structured linear maps*

Structured matrices have some properties that allow us to compute with them faster
than general dense matrices. Morphisms in this category represent structured matrices.
"""
@theory LinearFunctions(Ob,Hom) => StructuredLinearFunctions(Ob, Hom) begin
  munit()::Ob
  @op (ℝ) := munit

  diag(v)::(A→A) ⊣ (A::Ob, v::(ℝ()→A))
  upperdiag(v)::(A⊕ℝ() → A⊕ℝ()) ⊣ (A::Ob, v::(ℝ() → A))
  lowerdiag(v)::(A⊕ℝ() → A⊕ℝ()) ⊣ (A::Ob, v::(ℝ() → A))
  # lowerdiag(v, u)::(A⊕ℝ() → A⊕ℝ()) ⊣ (A::Ob, v::(ℝ() → A⊕ℝ()), u::(ℝ() → A))
  bidiag(v, u)::(A⊕ℝ() → A⊕ℝ()) ⊣ (A::Ob, v::(ℝ() → A⊕ℝ()), u::(ℝ() → A))
  tridiag(v, u, w)::(A⊕ℝ() → A⊕ℝ()) ⊣ (A::Ob, v::(ℝ() → A⊕ℝ()), u::(ℝ() → A), w::(ℝ() → A))
  symtridiag(v, u)::(A⊕ℝ() → A⊕ℝ()) ⊣ (A::Ob, v::(ℝ() → A⊕ℝ()), u::(ℝ() → A))
  #A is n-k and b is k in a n×n matrix with v on the kth diagonal
  upperdiag(A, v)::(A⊕B→A⊕B) ⊣ (A::Ob, B::Ob, v::(ℝ()→B))
  # A is n-k and b is k in a n×n matrix with v on the kth lower diagonal
  lowerdiag(A, v)::(A⊕B→A⊕B) ⊣ (A::Ob, B::Ob, v::(ℝ()→B))
  # Axioms
  lowerdiag == ⊟(upperdiag)
  upperdiag(A,b) == ◊(A) ⊕ diag(b) ⊕ mzero(A)  ⊣ (A::Ob, b::(ℝ()→B))
  lowerdiag(A,b) == mzero(A)  ⊕ diag(b) ⊕ ◊(A) ⊣ (A::Ob, b::(ℝ()→B))
  # by default upperdiagonal means 1-upperdiagonal
  upperdiag(b) == upperdiag(ℝ(), b) ⊣ (b::(ℝ()→B))
  # by default lowerdiagonal means 1-lowerdiagonal
  lowerdiag(b) == lowerdiag(ℝ(), b) ⊣ (b::(ℝ()→B))

  bidiag(a,b) == diag(a) + upperdiag(b) ⊣ (A::Ob, a::(ℝ()→A⊗ℝ()), b::(ℝ()→A))
  tridiag(a,b,c) == diag(a) + lowerdiag(b) + upperdiag(c) ⊣ (A::Ob, a::(ℝ()→A⊗ℝ()), b::(ℝ()→A), c::(ℝ()→A))
  symtridiag(a,b) == tridiagonal(a,b,b) ⊣ (A::Ob, a::(ℝ()→A⊗ℝ()), b::(ℝ()→A))
end

@syntax FreeStructuredLinearFunctions(ObExpr,HomExpr) StructuredLinearFunctions begin
  oplus(A::Ob, B::Ob) = associate_unit(new(A,B), mzero)
  oplus(f::Hom, g::Hom) = associate(new(f,g))
  compose(f::Hom, g::Hom) = new(f,g; strict=true) # No normalization!
end

end
