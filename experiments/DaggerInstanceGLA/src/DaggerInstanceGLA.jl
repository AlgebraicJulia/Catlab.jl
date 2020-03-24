module DaggerInstanceGLA

import Base: +
using AutoHashEquals

export LinearMapDom, LinearMap

using Dagger
using LinearAlgebra
using Catlab.LinearAlgebra.GraphicalLinearAlgebra
using Catlab
using LinearMaps
import LinearMaps: adjoint
const LMs = LinearMaps


@auto_hash_equals struct LinearMapDom
  N::Int
end

struct MatrixThunk
  thunk::Thunk
  size::Int
end

@instance LinearFunctions(LinearMapDom, MatrixThunk) begin
  @import adjoint

  +(f::MatrixThunk, g::MatrixThunk) = delayed(+)(f, g)

  dom(f::LinearMap) = LinearMapDom(size(f,2))
  codom(f::LinearMap) = LinearMapDom(size(f,1))

  compose(f::LinearMap, g::LinearMap) = g*f
  id(V::LinearMapDom) = LMs.UniformScalingMap(1, V.N)

  oplus(V::LinearMapDom, W::LinearMapDom) = LinearMapDom(V.N + W.N)
  oplus(f::LinearMap, g::LinearMap) = LMs.BlockDiagonalMap(f, g)
  mzero(::Type{LinearMapDom}) = LinearMapDom(0)
  braid(V::LinearMapDom, W::LinearMapDom) =
    LinearMap(braid_lm(V.N), braid_lm(W.N), W.N+V.N, V.N+W.N)

  mcopy(V::LinearMapDom) = LinearMap(mcopy_lm, plus_lm, 2*V.N, V.N)
  delete(V::LinearMapDom) = LinearMap(delete_lm, zero_lm(V.N), 0, V.N)
  plus(V::LinearMapDom) = LinearMap(plus_lm, mcopy_lm, V.N, 2*V.N)
  zero(V::LinearMapDom) = LinearMap(zero_lm(V.N), delete_lm, V.N, 0)

  plus(f::LinearMap, g::LinearMap) = f+g
  scalar(V::LinearMapDom, c::Number) = LMs.UniformScalingMap(c, V.N)
  antipode(V::LinearMapDom) = LMs.UniformScalingMap(-1, V.N)
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
