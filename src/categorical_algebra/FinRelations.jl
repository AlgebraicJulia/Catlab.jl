""" The category of finite sets and relations, and its skeleton.
"""
module FinRelations
export BoolRig, FinRel, FinRelation, FinRelationCallable, FinRelationMatrix,
  force

import Base: +, *
using AutoHashEquals

using ...GAT
using ...Theories: DistributiveBicategoryRelations
import ...Theories: dom, codom, id, compose, ⋅, ∘, dagger, dunit, dcounit,
  otimes, ⊗, munit, braid, oplus, ⊕, mzero, swap,
  mcopy, Δ, mmerge, ∇, delete, ◊, create, □, plus, zero, coplus, cozero,
  pair, copair, proj1, proj2, coproj1, coproj2, meet, join, top, bottom
import ..FinCats: force
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

# Category of finite relations
##############################

""" Object in the category of finite sets and relations.

See also: [`FinSet`](@ref).
"""
@auto_hash_equals struct FinRel{S,T}
  set::S
end

FinRel(i::Int) = FinRel{Int,Int}(i)
FinRel(set::S) where {T,S<:AbstractSet{T}} = FinRel{S,T}(set)

Base.eltype(::Type{FinRel{S,T}}) where {S,T} = T
Base.iterate(s::FinRel, args...) = iterate(iterable(s), args...)
Base.length(s::FinRel) = length(iterable(s))
Base.in(s::FinRel, elem) = in(s, iterable(s))
iterable(s::FinRel{Int}) = 1:s.set
iterable(s::FinRel{<:AbstractSet}) = s.set

""" Binary relation between finite sets.

A morphism in the category of finite sets and relations. The relation can be
represented implicitly by an arbitrary Julia function mapping pairs of elements
to booleans or explicitly by a matrix (dense or sparse) taking values in the rig
of booleans ([`BoolRig`](@ref)).
"""
abstract type FinRelation{S,S′,T,T′} end

FinRelation(R::Function, args...) = FinRelationCallable(R, args...)
FinRelation(R::AbstractMatrix, args...) = FinRelationMatrix(R, args...)

""" Relation in FinRel defined by a callable Julia object.
"""
@auto_hash_equals struct FinRelationCallable{S,S′,T,T′} <: FinRelation{S,S′,T,T′}
  # Field `rel` is usually a `Function` but can be any Julia callable.
  rel::Any
  dom::FinRel{S,T}
  codom::FinRel{S′,T′}

  FinRelationCallable(R, dom::FinRel{S,T}, codom::FinRel{S′,T′}) where {S,S′,T,T′} =
    new{S,S′,T,T′}(R, dom, codom)
end

FinRelationCallable(R, dom::Int, codom::Int) =
  FinRelationCallable(R, FinRel(dom), FinRel(codom))

(R::FinRelationCallable{S,T})(x::T, y::T) where {S,T} = R.rel(x, y)

""" Relation in FinRel represented by a boolean matrix.

Boolean matrices are also known as logical matrices or relation matrices.
"""
@auto_hash_equals struct FinRelationMatrix{M<:AbstractMatrix{BoolRig}} <: FinRelation{Int,Int,Int,Int}
  rel::M
end

function FinRelationMatrix(R::AbstractMatrix{BoolRig}, dom::Int, codom::Int)
  @assert size(R) == (dom, codom)
  FinRelationMatrix(R)
end
function FinRelationMatrix(R::AbstractMatrix{BoolRig},
                           dom::FinRel{Int}, codom::FinRel{Int})
  FinRelationMatrix(R, length(dom), length(codom))
end

(R::FinRelationMatrix)(x, y) = R.rel[y, x].value

function force(::Type{T}, R::FinRelation) where T <: AbstractMatrix{BoolRig}
  m, n = length(dom(R)), length(codom(R))
  M = zero_matrix(T, n, m)
  for i in 1:m, j in 1:n
    if R(i,j)
      M[j,i] = BoolRig(true)
    end
  end
  FinRelationMatrix(M)
end
force(::Type{T}, R::FinRelationMatrix{T}) where T <: AbstractMatrix{BoolRig} = R
force(R::FinRelation) = force(Matrix{BoolRig}, R)

""" FinRel as a distributive bicategory of relations.

FIXME: Many methods only work for `FinRel{Int}`. The default methods should
assume `FinRel{<:AbstractSet}` and the case `FinRel{Int}` should be handled
specially.
"""
@instance DistributiveBicategoryRelations{FinRel, FinRelation} begin
  dom(R::FinRelation) = R.dom
  codom(R::FinRelation) = R.codom

  id(A::FinRel) = FinRelation((x,y) -> x == y, A, A)

  function compose(R::FinRelation, S::FinRelation)
    @assert codom(R) == dom(S)
    FinRelation(dom(R), codom(S)) do x,z
      any(R(x,y) && S(y,z) for y in codom(R))
    end
  end
  
  # Multiplicative monoidal structure
  
  otimes(A::FinRel, B::FinRel) = FinRel(length(A) * length(B))
  munit(::Type{FinRel}) = FinRel(1)
   
  function otimes(R::FinRelation, S::FinRelation)
    # Indexing is consistent with that of Kronecker products.
    dom_proj = CartesianIndices((length(dom(S)), length(dom(R))))
    cod_proj = CartesianIndices((length(codom(S)), length(codom(R))))
    FinRelation(dom(R)⊗dom(S), codom(R)⊗codom(S)) do x, y
      R(dom_proj[x][2], cod_proj[y][2]) && S(dom_proj[x][1], cod_proj[y][1])
    end
  end
  
  function braid(A::FinRel, B::FinRel)
    dom_proj = CartesianIndices((length(B), length(A)))
    cod_proj = CartesianIndices((length(A), length(B)))
    FinRelation(A⊗B, B⊗A) do x, y
      dom_proj[x][1] == cod_proj[y][2] && dom_proj[x][2] == cod_proj[y][1]
    end
  end
  
  function mcopy(A::FinRel)
    n = length(A)
    proj = CartesianIndices((n, n))
    FinRelation((x,y) -> x == proj[y][1] && x == proj[y][2], A, A⊗A)
  end
  function mmerge(A::FinRel)
    n = length(A)
    proj = CartesianIndices((n, n))
    FinRelation((x,y) -> proj[x][1] == y && proj[x][2] == y, A⊗A, A)
  end
  delete(A::FinRel) = FinRelation((x,y) -> true, A, munit(FinRel))
  create(A::FinRel) = FinRelation((x,y) -> true, munit(FinRel), A)
  
  dagger(R::FinRelation) = FinRelation((x,y) -> R(y,x), codom(R), dom(R))
  dunit(A::FinRel) = compose(create(A), mcopy(A))
  dcounit(A::FinRel) = compose(mmerge(A), delete(A))
  
  # Additive monoidal structure
  
  oplus(A::FinRel, B::FinRel) = FinRel(length(A) + length(B))
  mzero(::Type{FinRel}) = FinRel(0)
  
  function oplus(R::FinRelation, S::FinRelation)
    m, n = length(dom(R)), length(codom(R))
    FinRelation(dom(R)⊕dom(S), codom(R)⊕codom(S)) do x, y
      (x <= m && y <= n && R(x, y)) || (x > m && y > n && S(x-m, y-n))
    end
  end
  
  function swap(A::FinRel, B::FinRel)
    m, n = length(A), length(B)
    FinRelation((x,y) -> x == y-n || x-m == y, A⊕B, B⊕A)
  end
  
  function plus(A::FinRel)
    n = length(A)
    FinRelation((x,y) -> x == y || x-n == y, A⊕A, A)
  end
  function coplus(A::FinRel)
    n = length(A)
    FinRelation((x,y) -> x == y || x == y-n, A, A⊕A)
  end
  zero(A::FinRel) = FinRelation((x,y) -> false, mzero(FinRel), A)
  cozero(A::FinRel) = FinRelation((x,y) -> false, A, mzero(FinRel))
  
  pair(R::FinRelation, S::FinRelation) = coplus(dom(R))⋅(R⊕S)
  copair(R::FinRelation, S::FinRelation) = (R⊕S)⋅plus(codom(R))
  proj1(A::FinRel, B::FinRel) = id(A)⊕cozero(B)
  proj2(A::FinRel, B::FinRel) = cozero(A)⊕id(B)
  coproj1(A::FinRel, B::FinRel) = id(A)⊕zero(B)
  coproj2(A::FinRel, B::FinRel) = zero(A)⊕id(B)
  
  # Lattice structure
  
  function meet(R::FinRelation, S::FinRelation)
    @assert dom(R) == dom(S) && codom(R) == codom(S)
    FinRelation((x,y) -> R(x,y) && S(x,y), dom(R), codom(R))
  end
  function join(R::FinRelation, S::FinRelation)
    @assert dom(R) == dom(S) && codom(R) == codom(S)
    FinRelation((x,y) -> R(x,y) || S(x,y), dom(R), codom(R))
  end
  top(A::FinRel, B::FinRel) = FinRelation((x,y) -> true, A, B)
  bottom(A::FinRel, B::FinRel) = FinRelation((x,y) -> false, A, B)
end

# For relation matrices, delegate to the category of matrices.
const FinRelMat = FinRelationMatrix

dom(R::FinRelMat) = FinRel(size(R.rel, 2))
codom(R::FinRelMat) = FinRel(size(R.rel, 1))

compose(R::FinRelMat, S::FinRelMat) = FinRelMat(compose(R.rel, S.rel))
otimes(R::FinRelMat, S::FinRelMat) = FinRelMat(otimes(R.rel, S.rel))
oplus(R::FinRelMat, S::FinRelMat) = FinRelMat(oplus(R.rel, S.rel))
dagger(R::FinRelMat) = FinRelMat(transpose(R.rel))

meet(R::FinRelMat, S::FinRelMat) = FinRelMat(R.rel .* S.rel)
join(R::FinRelMat, S::FinRelMat) = FinRelMat(R.rel .+ S.rel)
pair(R::FinRelMat, S::FinRelMat) = FinRelMat(pair(R.rel, S.rel))
copair(R::FinRelMat, S::FinRelMat) = FinRelMat(copair(R.rel, S.rel))

end
