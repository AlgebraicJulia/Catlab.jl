""" Computing in the category of finite sets and relations, and its skeleton.
"""
module FinRelations
export BoolRig, FinOrdRelOb, FinOrdRelation, force

import Base: +, *
using AutoHashEquals

using ...GAT
using ...Theories: SymmetricMonoidalCategory
import ...Theories: dom, codom, id, compose, ⋅, ∘, otimes, ⊗, munit, braid,
  mcopy, Δ, mmerge, ∇, delete, ◊, create, □
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
@auto_hash_equals struct FinOrdRelationLazy <: FinOrdRelation
  rel::Function
  dom::Int
  codom::Int
end
FinOrdRelation(R::Function, dom::Int, codom::Int) =
  FinOrdRelationLazy(R, dom, codom)

(R::FinOrdRelationLazy)(x, y) = R.rel(x, y)

""" Relation in FinOrdRel represented by a boolean matrix.

Boolean matrices are also known as logical matrices or relation matrices.
"""
@auto_hash_equals struct FinOrdRelationMatrix{T <: AbstractMatrix{BoolRig}} <: FinOrdRelation
  rel::T
end

FinOrdRelation(R::AbstractMatrix{BoolRig}) = FinOrdRelationMatrix(R)

function FinOrdRelation(R::AbstractMatrix{BoolRig}, dom::Int, codom::Int)
  @assert size(R,2) == dom && size(R,1) == codom
  FinOrdRelationMatrix(R)
end

(R::FinOrdRelationMatrix)(x, y) = R.rel[y, x].value

function force(::Type{T}, R::FinOrdRelation) where T <: AbstractMatrix{BoolRig}
  m, n = dom(R).n, codom(R).n
  M = zero_matrix(T, n, m)
  for i in 1:m, j in 1:n
    if R(i,j)
      M[j,i] = BoolRig(true)
    end
  end
  FinOrdRelationMatrix(M)
end
force(::Type{T}, R::FinOrdRelationMatrix{T}) where T <: AbstractMatrix{BoolRig} = R
force(R::FinOrdRelation) = force(Matrix{BoolRig}, R)

""" FinOrdRel as a bicategory of relations.
"""
@instance SymmetricMonoidalCategory(FinOrdRelOb, FinOrdRelation) begin
  dom(R::FinOrdRelation) = FinOrdRelOb(R.dom)
  codom(R::FinOrdRelation) = FinOrdRelOb(R.codom)

  id(A::FinOrdRelOb) = FinOrdRelation((x1,x2) -> x1 == x2, A, A)

  function compose(R::FinOrdRelation, S::FinOrdRelation)
    @assert codom(R) == dom(S)
    rel = (x,z) -> any(R(x,y) && S(y,z) for y in eachindex(codom(R)))
    FinOrdRelation(rel, dom(R), codom(S))
  end
  
  otimes(A::FinOrdRelOb, B::FinOrdRelOb) = FinOrdRelOb(A.n * B.n)
  munit(::Type{FinOrdRelOb}) = FinOrdRelOb(1)
   
  function otimes(R::FinOrdRelation, S::FinOrdRelation)
    # Indexing is consistent with that of Kronecker products.
    dom_proj = CartesianIndices((dom(S).n, dom(R).n))
    cod_proj = CartesianIndices((codom(S).n, codom(R).n))
    rel = (x,y) -> (R(dom_proj[x][2], cod_proj[y][2]) &&
                    S(dom_proj[x][1], cod_proj[y][1]))
    FinOrdRelation(rel, dom(R)⊗dom(S), codom(R)⊗codom(S))
  end
  
  function braid(A::FinOrdRelOb, B::FinOrdRelOb)
    dom_proj = CartesianIndices((B.n, A.n))
    cod_proj = CartesianIndices((A.n, B.n))
    rel = (x,y) -> (dom_proj[x][1] == cod_proj[y][2] &&
                    dom_proj[x][2] == cod_proj[y][1])
    FinOrdRelation(rel, A⊗B, B⊗A)
  end
end

dom(R::FinOrdRelationMatrix) = FinOrdRelOb(size(R.rel, 2))
codom(R::FinOrdRelationMatrix) = FinOrdRelOb(size(R.rel, 1))

# For relation matrices, delegate to general category of matrices.
compose(R::FinOrdRelationMatrix, S::FinOrdRelationMatrix) =
  FinOrdRelationMatrix(compose(R.rel, S.rel))
otimes(R::FinOrdRelationMatrix, S::FinOrdRelationMatrix) =
  FinOrdRelationMatrix(otimes(R.rel, S.rel))

end
