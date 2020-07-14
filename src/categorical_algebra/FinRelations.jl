""" Computing in the category of finite sets and relations, and its skeleton.
"""
module FinRelations
export BoolRig, FinOrdRelOb, FinOrdRelation, FinOrdPredicate, FinOrdMatrix,
  force

import Base: +, *
using AutoHashEquals

using ...GAT
using ...Theories: DistributiveBicategoryRelations
import ...Theories: dom, codom, id, compose, ⋅, ∘, dagger, dunit, dcounit,
  otimes, ⊗, munit, braid, oplus, ⊕, mzero, swap,
  mcopy, Δ, mmerge, ∇, delete, ◊, create, □, plus, zero, coplus, cozero,
  pair, copair, proj1, proj2, coproj1, coproj2, meet, join, top, bottom
import ..FinSets: force
using ..Matrices
using ..Matrices: zero_matrix

# Rig of booleans
#################

""" The rig of booleans.

This struct is needed because in base Julia, the product of booleans is another
boolean, but the sum of booleans is coerced to an integer: `true + true == 2`.
"""
@auto_hash_equals struct BoolRig <: Number
  value::Bool
end

+(x::BoolRig, y::BoolRig) = BoolRig(x.value || y.value)
*(x::BoolRig, y::BoolRig) = BoolRig(x.value && y.value)

Base.zero(::Type{BoolRig}) = BoolRig(false)
Base.one(::Type{BoolRig}) = BoolRig(true)
Base.float(x::BoolRig) = float(x.value)
Base.show(io::IO, x::BoolRig) = print(io, x.value)

# Category of finite ordinals and relations
###########################################

""" Finite ordinal (natural number).

An object in the category `FinOrdRel` of finite ordinals and relations, which is
the skeleton of the category `FinRel` of finite sets and relations.
"""
@auto_hash_equals struct FinOrdRelOb
  n::Int
end
Base.eachindex(X::FinOrdRelOb) = 1:X.n

""" Binary relation between sets in the form of finite ordinals.

A morphism in the category `FinOrdRel` of finite ordinals and relations, which
is the skeleton of the category `FinRel` of finite sets and relations. The
relation can be represented implicitly by an arbitrary Julia function mapping
pairs of integers to booleans or explicitly by a matrix (dense or sparse) taking
values in the rig of booleans ([`BoolRig`](@ref)).
"""
abstract type FinOrdRelation end

FinOrdRelation(R, dom::FinOrdRelOb, codom::FinOrdRelOb) =
  FinOrdRelation(R, dom.n, codom.n)

""" Relation in FinOrdRel represented by an arbitrary Julia function.
"""
@auto_hash_equals struct FinOrdPredicate <: FinOrdRelation
  rel::Function
  dom::Int
  codom::Int
end
FinOrdRelation(R::Function, dom::Int, codom::Int) =
  FinOrdPredicate(R, dom, codom)

(R::FinOrdPredicate)(x, y) = R.rel(x, y)

""" Relation in FinOrdRel represented by a boolean matrix.

Boolean matrices are also known as logical matrices or relation matrices.
"""
@auto_hash_equals struct FinOrdMatrix{T <: AbstractMatrix{BoolRig}} <: FinOrdRelation
  rel::T
end

FinOrdRelation(R::AbstractMatrix{BoolRig}) = FinOrdMatrix(R)

function FinOrdRelation(R::AbstractMatrix{BoolRig}, dom::Int, codom::Int)
  @assert size(R,2) == dom && size(R,1) == codom
  FinOrdMatrix(R)
end

(R::FinOrdMatrix)(x, y) = R.rel[y, x].value

function force(::Type{T}, R::FinOrdRelation) where T <: AbstractMatrix{BoolRig}
  m, n = dom(R).n, codom(R).n
  M = zero_matrix(T, n, m)
  for i in 1:m, j in 1:n
    if R(i,j)
      M[j,i] = BoolRig(true)
    end
  end
  FinOrdMatrix(M)
end
force(::Type{T}, R::FinOrdMatrix{T}) where T <: AbstractMatrix{BoolRig} = R
force(R::FinOrdRelation) = force(Matrix{BoolRig}, R)

""" FinOrdRel as a distributive bicategory of relations.
"""
@instance DistributiveBicategoryRelations(FinOrdRelOb, FinOrdRelation) begin
  dom(R::FinOrdRelation) = FinOrdRelOb(R.dom)
  codom(R::FinOrdRelation) = FinOrdRelOb(R.codom)

  id(A::FinOrdRelOb) = FinOrdRelation((x,y) -> x == y, A, A)

  function compose(R::FinOrdRelation, S::FinOrdRelation)
    @assert codom(R) == dom(S)
    FinOrdRelation(dom(R), codom(S)) do x,z
      any(R(x,y) && S(y,z) for y in eachindex(codom(R)))
    end
  end
  
  # Multiplicative monoidal structure
  
  otimes(A::FinOrdRelOb, B::FinOrdRelOb) = FinOrdRelOb(A.n * B.n)
  munit(::Type{FinOrdRelOb}) = FinOrdRelOb(1)
   
  function otimes(R::FinOrdRelation, S::FinOrdRelation)
    # Indexing is consistent with that of Kronecker products.
    dom_proj = CartesianIndices((dom(S).n, dom(R).n))
    cod_proj = CartesianIndices((codom(S).n, codom(R).n))
    FinOrdRelation(dom(R)⊗dom(S), codom(R)⊗codom(S)) do x, y
      R(dom_proj[x][2], cod_proj[y][2]) && S(dom_proj[x][1], cod_proj[y][1])
    end
  end
  
  function braid(A::FinOrdRelOb, B::FinOrdRelOb)
    dom_proj = CartesianIndices((B.n, A.n))
    cod_proj = CartesianIndices((A.n, B.n))
    FinOrdRelation(A⊗B, B⊗A) do x, y
      dom_proj[x][1] == cod_proj[y][2] && dom_proj[x][2] == cod_proj[y][1]
    end
  end
  
  function mcopy(A::FinOrdRelOb)
    proj = CartesianIndices((A.n, A.n))
    FinOrdRelation((x,y) -> x == proj[y][1] && x == proj[y][2], A, A⊗A)
  end
  function mmerge(A::FinOrdRelOb)
    proj = CartesianIndices((A.n, A.n))
    FinOrdRelation((x,y) -> proj[x][1] == y && proj[x][2] == y, A⊗A, A)
  end
  delete(A::FinOrdRelOb) = FinOrdRelation((x,y) -> true, A, munit(FinOrdRelOb))
  create(A::FinOrdRelOb) = FinOrdRelation((x,y) -> true, munit(FinOrdRelOb), A)
  
  dagger(R::FinOrdRelation) = FinOrdRelation((x,y) -> R(y,x), codom(R), dom(R))
  dunit(A::FinOrdRelOb) = compose(create(A), mcopy(A))
  dcounit(A::FinOrdRelOb) = compose(mmerge(A), delete(A))
  
  # Additive monoidal structure
  
  oplus(A::FinOrdRelOb, B::FinOrdRelOb) = FinOrdRelOb(A.n + B.n)
  mzero(::Type{FinOrdRelOb}) = FinOrdRelOb(0)
  
  function oplus(R::FinOrdRelation, S::FinOrdRelation)
    m, n = dom(R).n, codom(R).n
    FinOrdRelation(dom(R)⊕dom(S), codom(R)⊕codom(S)) do x, y
      (x <= m && y <= n && R(x, y)) || (x > m && y > n && S(x-m, y-n))
    end
  end
  
  function swap(A::FinOrdRelOb, B::FinOrdRelOb)
    FinOrdRelation((x,y) -> x == y-B.n || x-A.n == y, A⊕B, B⊕A)
  end
  
  plus(A::FinOrdRelOb) = FinOrdRelation((x,y) -> x == y || x-A.n == y, A⊕A, A)
  coplus(A::FinOrdRelOb) = FinOrdRelation((x,y) -> x == y || x == y-A.n, A, A⊕A)
  zero(A::FinOrdRelOb) = FinOrdRelation((x,y) -> false, mzero(FinOrdRelOb), A)
  cozero(A::FinOrdRelOb) = FinOrdRelation((x,y) -> false, A, mzero(FinOrdRelOb))
  
  pair(R::FinOrdRelation, S::FinOrdRelation) = coplus(dom(R))⋅(R⊕S)
  copair(R::FinOrdRelation, S::FinOrdRelation) = (R⊕S)⋅plus(codom(R))
  proj1(A::FinOrdRelOb, B::FinOrdRelOb) = id(A)⊕cozero(B)
  proj2(A::FinOrdRelOb, B::FinOrdRelOb) = cozero(A)⊕id(B)
  coproj1(A::FinOrdRelOb, B::FinOrdRelOb) = id(A)⊕zero(B)
  coproj2(A::FinOrdRelOb, B::FinOrdRelOb) = zero(A)⊕id(B)
  
  # Lattice structure
  
  function meet(R::FinOrdRelation, S::FinOrdRelation)
    @assert dom(R) == dom(S) && codom(R) == codom(S)
    FinOrdRelation((x,y) -> R(x,y) && S(x,y), dom(R), codom(R))
  end
  function join(R::FinOrdRelation, S::FinOrdRelation)
    @assert dom(R) == dom(S) && codom(R) == codom(S)
    FinOrdRelation((x,y) -> R(x,y) || S(x,y), dom(R), codom(R))
  end
  top(A::FinOrdRelOb, B::FinOrdRelOb) = FinOrdRelation((x,y) -> true, A, B)
  bottom(A::FinOrdRelOb, B::FinOrdRelOb) = FinOrdRelation((x,y) -> false, A, B)
end

# For relation matrices, delegate to the category of matrices.
dom(R::FinOrdMatrix) = FinOrdRelOb(size(R.rel, 2))
codom(R::FinOrdMatrix) = FinOrdRelOb(size(R.rel, 1))

compose(R::FinOrdMatrix, S::FinOrdMatrix) = FinOrdMatrix(compose(R.rel, S.rel))
otimes(R::FinOrdMatrix, S::FinOrdMatrix) = FinOrdMatrix(otimes(R.rel, S.rel))
oplus(R::FinOrdMatrix, S::FinOrdMatrix) = FinOrdMatrix(oplus(R.rel, S.rel))
dagger(R::FinOrdMatrix) = FinOrdMatrix(transpose(R.rel))

meet(R::FinOrdMatrix, S::FinOrdMatrix) = FinOrdMatrix(R.rel .* S.rel)
join(R::FinOrdMatrix, S::FinOrdMatrix) = FinOrdMatrix(R.rel .+ S.rel)
pair(R::FinOrdMatrix, S::FinOrdMatrix) = FinOrdMatrix(pair(R.rel, S.rel))
copair(R::FinOrdMatrix, S::FinOrdMatrix) = FinOrdMatrix(copair(R.rel, S.rel))

end
