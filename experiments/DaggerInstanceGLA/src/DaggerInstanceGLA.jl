module DaggerInstanceGLA

import Base: +
using AutoHashEquals

export DagDom, LinearMap, MatrixThunk, matrixToThunk,
       dom, codom, adjoint, +, compose, id, oplus, mzero,
       braid, mcopy, delete, plus, zero, scalar, antipode,
       ⊗
using Dagger
using LinearAlgebra
using Catlab.LinearAlgebra.GraphicalLinearAlgebra
using Catlab, Catlab.Doctrines
import ...Doctrines:
  Ob, Hom, dom, codom, compose, ⋅, ∘, id, oplus, ⊕, mzero, braid,
  dagger, dunit, dcounit, mcopy, Δ, delete, ◊, mmerge, ∇, create, □,
  plus, zero, coplus, cozero, meet, top, join, bottom
using LinearMaps
import LinearMaps: adjoint
const LMs = LinearMaps


@auto_hash_equals struct DagDom
  N::Int
end

# This structure was created to keep track of dom and codom information.
# This information can be updated efficiently, and keeping it here keeps
# LinearFunctions from having to think the thunk each time the dom or codom
# is queried

struct MatrixThunk
  thunk::Thunk
  dom::Int
  codom::Int
end

matrixToThunk(A::LinearMap) = begin
  delayed(x->x)(A)
end

@instance LinearFunctions(DagDom, MatrixThunk) begin

  adjoint(f::MatrixThunk) = MatrixThunk(delayed(adjoint)(f.thunk), f.codom, f.dom)
  +(f::MatrixThunk, g::MatrixThunk) = MatrixThunk(delayed(+)(f.thunk, g.thunk), f.dom, f.codom)

  dom(f::MatrixThunk) = f.dom
  codom(f::MatrixThunk) = f.codom

  compose(f::MatrixThunk, g::MatrixThunk) = MatrixThunk(delayed(*)(g.thunk,f.thunk), g.dom, f.codom)
  id(V::DagDom) = MatrixThunk(delayed(x->x)(LMs.UniformScalingMap(1, V.N)), V.N, V.N)

  oplus(V::DagDom, W::DagDom) = DagDom(V.N + W.N)
  oplus(f::MatrixThunk, g::MatrixThunk) = MatrixThunk(delayed(LMs.BlockDiagonalMap)(f.thunk, g.thunk), f.dom+g.dom, f.codom+g.codom)
  mzero(::Type{DagDom}) = DagDom(0)
  braid(V::DagDom, W::DagDom) =
  MatrixThunk(delayed(x->x)(LinearMap(braid_lm(V.N), braid_lm(W.N), W.N+V.N, V.N+W.N)),V.N+W.N, W.N+V.N)

  mcopy(V::DagDom)  = MatrixThunk(delayed(x->x)(LinearMap(mcopy_lm, plus_lm, 2*V.N, V.N)), V.N, 2*V.N)
  delete(V::DagDom) = MatrixThunk(delayed(x->x)(LinearMap(delete_lm, zero_lm(V.N), 0, V.N)), V.N, 0)
  plus(V::DagDom)   = MatrixThunk(delayed(x->x)(LinearMap(plus_lm, mcopy_lm, V.N, 2*V.N)), 2*V.N, V.N)
  zero(V::DagDom)   = MatrixThunk(delayed(x->x)(LinearMap(zero_lm(V.N), delete_lm, V.N, 0)), 0, V.N)

  plus(f::MatrixThunk, g::MatrixThunk) = f+g
  scalar(V::DagDom, c::Number) = MatrixThunk(delayed(x->x)(LMs.UniformScalingMap(c, V.N)), V.N, V.N)
  antipode(V::DagDom) = scalar(V, -1)
end

braid_lm(n::Int) = x::AbstractVector -> vcat(x[n+1:end], x[1:n])
mcopy_lm(x::AbstractVector) = vcat(x, x)
delete_lm(x::AbstractVector) = eltype(x)[]
plus_lm(x::AbstractVector) = begin
  n = length(x) ÷ 2
  x[1:n] + x[n+1:end]
end
zero_lm(n::Int) = x::AbstractVector -> zeros(eltype(x), n)

end
