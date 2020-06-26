module GraphicalLinearAlgebra
export LinearFunctions, FreeLinearFunctions, LinearRelations,
  FreeLinearRelations, LinearMapDom, LinearMap, LinearOpDom, LinearOperator,
  Ob, Hom, dom, codom, compose, ⋅, ∘, id, oplus, ⊕, mzero, swap,
  dagger, dunit, docunit, mcopy, Δ, delete, ◊, mmerge, ∇, create, □,
  plus, +, zero, coplus, cozero, meet, top, join, bottom,
  scalar, antipode, antipode, adjoint, evaluate

using AutoHashEquals
using LinearMaps
import LinearMaps: adjoint
const LMs = LinearMaps
using LinearOperators
import LinearOperators:
  adjoint, opEye, opExtension, opRestriction, opZeros

using ...Catlab, ...Theories
import ...Theories:
  Ob, Hom, dom, codom, compose, ⋅, ∘, id, oplus, ⊕, mzero, swap,
  dagger, dunit, dcounit, mcopy, Δ, delete, ◊, mmerge, ∇, create, □,
  plus, +, zero, coplus, cozero, meet, top, join, bottom
using ...Programs
import ...Programs: evaluate_hom

# Theories
###########

""" Theory of *linear functions*, aka linear maps

Functional fragment of graphical linear algebra.
"""
@theory SemiadditiveCategory(Ob,Hom) => LinearFunctions(Ob,Hom) begin
  adjoint(f::(A → B))::(B → A) ⊣ (A::Ob, B::Ob)
  
  scalar(A::Ob, c::Number)::(A → A)
  antipode(A::Ob)::(A → A)

  # Scalar and antipode axioms.
  scalar(A, a) ⋅ scalar(A, b) == scalar(A, a*b) ⊣ (A::Ob, a::Number, b::Number)
  scalar(A, 1) == id(A) ⊣ (A::Ob)
  scalar(A, a) ⋅ Δ(A) == Δ(A) ⋅ (scalar(A, a) ⊕ scalar(A, a)) ⊣ (A::Ob, a::Number)
  scalar(A, a) ⋅ ◊(A) == ◊(A) ⊣ (A::Ob, a::Number)
  Δ(A) ⋅ (scalar(A, a) ⊕ scalar(A, b)) ⋅ plus(A) == scalar(A, a+b) ⊣ (A::Ob, a::Number, b::Number)
  scalar(A, 0) == ◊(A) ⋅ zero(A) ⊣ (A::Ob)
  zero(A) ⋅ scalar(A, a) == zero(A) ⊣ (A::Ob, a::Number)
  antipode(A) == scalar(A, -1) ⊣ (A::Ob)

  # Homogeneity axiom. Additivity is inherited from `SemiadditiveCategory`.
  scalar(A, c) ⋅ f == f ⋅ scalar(B, c) ⊣ (A::Ob, B::Ob, c::Number, f::(A → B))
end

@syntax FreeLinearFunctions(ObExpr,HomExpr) LinearFunctions begin
  oplus(A::Ob, B::Ob) = associate_unit(new(A,B), mzero)
  oplus(f::Hom, g::Hom) = associate(new(f,g))
  compose(f::Hom, g::Hom) = new(f,g; strict=true) # No normalization!
end

""" Theory of *linear relations*

The full relational language of graphical linear algebra.
"""
@theory AbelianBicategoryRelations(Ob,Hom) => LinearRelations(Ob,Hom) begin
  adjoint(R::(A → B))::(B → A) ⊣ (A::Ob, B::Ob)

  scalar(A::Ob, c::Number)::(A → A)
  antipode(A::Ob)::(A → A)

  # Linearity axioms.
  plus(A)⋅R == (R⊕R)⋅plus(B) ⊣ (A::Ob, B::Ob, R::(A → B))
  zero(A)⋅R == zero(B) ⊣ (A::Ob, B::Ob, R::(A → B))
  scalar(A, c) ⋅ R == R ⋅ scalar(B, c) ⊣ (A::Ob, B::Ob, c::Number, R::(A → B))
end

@syntax FreeLinearRelations(ObExpr,HomExpr) LinearRelations begin
  oplus(A::Ob, B::Ob) = associate_unit(new(A,B), mzero)
  oplus(R::Hom, S::Hom) = associate(new(R,S))
  compose(R::Hom, S::Hom) = new(R,S; strict=true) # No normalization!
end

# Evaluation
############

# LinearMaps instance
#--------------------

@auto_hash_equals struct LinearMapDom
  N::Int
end

@instance LinearFunctions(LinearMapDom, LinearMap) begin
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

# LinearOps instance
#-------------------

@auto_hash_equals struct LinearOpDom
  N::Int
end

@instance LinearFunctions(LinearOpDom, LinearOperator) begin
  @import adjoint, +

  dom(f::LinearOperator) = LinearOpDom(size(f,2))
  codom(f::LinearOperator) = LinearOpDom(size(f,1))

  compose(f::LinearOperator, g::LinearOperator) = g*f
  id(V::LinearOpDom) = opEye(V.N)

  oplus(V::LinearOpDom, W::LinearOpDom) = LinearOpDom(V.N + W.N)
  oplus(f::LinearOperator, g::LinearOperator) = begin
    dom_total   = size(f,2) + size(g,2)
    codom_total = size(f,1) + size(g,1)
    dom_f   = 1:size(f,2)
    codom_f = 1:size(f,1)
    dom_g   = (size(f,2)+1):dom_total
    codom_g = (size(f,1)+1):codom_total
    fOp = opExtension(codom_f, codom_total)*f*opRestriction(dom_f,dom_total)
    gOp = opExtension(codom_g, codom_total)*g*opRestriction(dom_g,dom_total)
    fOp + gOp
  end
  mzero(::Type{LinearOpDom}) = LinearOpDom(0)
  swap(V::LinearOpDom, W::LinearOpDom) =
    opExtension(1:W.N, V.N+W.N) * opRestriction((V.N+1):(V.N+W.N),V.N+W.N) +
    opExtension((W.N+1):(V.N+W.N), V.N+W.N) * opRestriction(1:V.N,V.N+W.N)
  mcopy(V::LinearOpDom) =
    opExtension(1:V.N, 2*V.N)+opExtension((V.N+1):(2*V.N), 2*V.N)
  delete(V::LinearOpDom) = opZeros(0, V.N)
  plus(V::LinearOpDom) =
    opRestriction(1:V.N, 2*V.N)+opRestriction((V.N+1):(2*V.N), 2*V.N)
  zero(V::LinearOpDom) = opZeros(V.N, 0)

  plus(f::LinearOperator, g::LinearOperator) = f+g
  scalar(V::LinearOpDom, c::Number) = opEye(typeof(c),V.N)*c
  antipode(V::LinearOpDom) = scalar(V,-1)
  
  pair(f::LinearOperator, g::LinearOperator) = mcopy(dom(f)) ⋅ (f ⊕ g)
  copair(f::LinearOperator, g::LinearOperator) = (f ⊕ g) ⋅ plus(codom(f))
  proj1(A::LinearOpDom, B::LinearOpDom) = id(A) ⊕ delete(B)
  proj2(A::LinearOpDom, B::LinearOpDom) = delete(A) ⊕ id(B)
  coproj1(A::LinearOpDom, B::LinearOpDom) = id(A) ⊕ zero(B)
  coproj2(A::LinearOpDom, B::LinearOpDom) = zero(A) ⊕ id(B)
end

# Catlab evaluate
#----------------

function evaluate_hom(f::FreeLinearFunctions.Hom{:generator}, xs::Vector;
                      generators::AbstractDict=Dict())
  M = generators[f]
  x = reduce(vcat, xs; init=eltype(M)[])
  [ M*x ]
end

function evaluate_hom(f::FreeLinearFunctions.Hom{:plus}, xs::Vector; kw...)
  if first(f) isa ObExpr
    # Addition map.
    [ reduce(+, xs) ]
  else
    # Sum of linear maps.
    mapreduce(+, args(f)) do g
      evaluate_hom(g, xs; kw...)
    end
  end
end
function evaluate_hom(f::FreeLinearFunctions.Hom{:zero}, xs::Vector;
                      generators::AbstractDict=Dict())
  map(collect(codom(f))) do A
    dims = generators[A]
    zeros(dims...)
  end
end

evaluate_hom(f::FreeLinearFunctions.Hom{:scalar}, xs::Vector; kw...) = last(f) .* xs
evaluate_hom(f::FreeLinearFunctions.Hom{:antipode}, xs::Vector; kw...) = -1 .* xs

end
