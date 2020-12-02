# External packages.
import .LinearMaps
using .LinearMaps: LinearMap

const LMs = LinearMaps


@auto_hash_equals struct LinearMapDom
  N::Int
end

@instance LinearFunctions{LinearMapDom, LinearMap} begin
  @import adjoint, +

  dom(f::LinearMap) = LinearMapDom(size(f,2))
  codom(f::LinearMap) = LinearMapDom(size(f,1))

  compose(f::LinearMap, g::LinearMap) = g*f
  id(V::LinearMapDom) = LMs.UniformScalingMap(1, V.N)

  oplus(V::LinearMapDom, W::LinearMapDom) = LinearMapDom(V.N + W.N)
  oplus(f::LinearMap, g::LinearMap) = LMs.BlockDiagonalMap(f, g)
  mzero(::Type{LinearMapDom}) = LinearMapDom(0)
  swap(V::LinearMapDom, W::LinearMapDom) =
    LinearMap(swap_lm(V.N), swap_lm(W.N), W.N+V.N, V.N+W.N)

  mcopy(V::LinearMapDom) = LinearMap(mcopy_lm, plus_lm, 2*V.N, V.N)
  delete(V::LinearMapDom) = LinearMap(delete_lm, zero_lm(V.N), 0, V.N)
  plus(V::LinearMapDom) = LinearMap(plus_lm, mcopy_lm, V.N, 2*V.N)
  zero(V::LinearMapDom) = LinearMap(zero_lm(V.N), delete_lm, V.N, 0)

  plus(f::LinearMap, g::LinearMap) = f+g
  scalar(V::LinearMapDom, c::Number) = LMs.UniformScalingMap(c, V.N)
  antipode(V::LinearMapDom) = LMs.UniformScalingMap(-1, V.N)

  pair(f::LinearMap, g::LinearMap) = mcopy(dom(f)) ⋅ (f ⊕ g)
  copair(f::LinearMap, g::LinearMap) = (f ⊕ g) ⋅ plus(codom(f))
  proj1(A::LinearMapDom, B::LinearMapDom) = id(A) ⊕ delete(B)
  proj2(A::LinearMapDom, B::LinearMapDom) = delete(A) ⊕ id(B)
  coproj1(A::LinearMapDom, B::LinearMapDom) = id(A) ⊕ zero(B)
  coproj2(A::LinearMapDom, B::LinearMapDom) = zero(A) ⊕ id(B)
end

swap_lm(n::Int) = x::AbstractVector -> vcat(x[n+1:end], x[1:n])
mcopy_lm(x::AbstractVector) = vcat(x, x)
delete_lm(x::AbstractVector) = eltype(x)[]
plus_lm(x::AbstractVector) = begin
  n = length(x) ÷ 2
  x[1:n] + x[n+1:end]
end
zero_lm(n::Int) = x::AbstractVector -> zeros(eltype(x), n)
