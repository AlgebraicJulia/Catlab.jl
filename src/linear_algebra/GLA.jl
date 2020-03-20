module GraphicalLinearAlgebra
export LinearFunctions, FreeLinearFunctions, LinearRelations,
  FreeLinearRelations, LinearMapDom, LinearMap,
  LinearOpDom, LinearOperator,
  Ob, Hom, dom, codom, compose, ⋅, ∘, id, oplus, ⊕, mzero, braid,
  dagger, dunit, docunit, mcopy, Δ, delete, ◊, mmerge, ∇, create, □,
  pplus, zero, coplus, cozero, plus, +, meet, top, join, bottom,
  scalar, antipode, antipode, adjoint, evaluate

import Base: +
using AutoHashEquals
using LinearMaps
import LinearMaps: adjoint
const LMs = LinearMaps
using LinearOperators
import LinearOperators:
  adjoint, opEye, opExtension, opRestriction, opZeros

using ...Catlab, ...Doctrines
import ...Doctrines:
  Ob, Hom, dom, codom, compose, ⋅, ∘, id, oplus, ⊕, mzero, braid,
  dagger, dunit, dcounit, mcopy, Δ, delete, ◊, mmerge, ∇, create, □,
  plus, zero, coplus, cozero, meet, top, join, bottom
using ...Programs
import ...Programs: evaluate_hom

# Doctrines
###########

""" Doctrine of *linear functions*, aka linear maps

Functional fragment of graphical linear algebra.
"""
@theory AdditiveSymmetricMonoidalCategory(Ob,Hom) => LinearFunctions(Ob,Hom) begin
  # Copying and deleting maps.
  mcopy(A::Ob)::(A → (A ⊕ A))
  @op (Δ) := mcopy
  delete(A::Ob)::(A → mzero())
  @op (◊) := delete

  # Addition and zero maps.
  plus(A::Ob)::((A ⊕ A) → A)
  @op (+) := plus
  zero(A::Ob)::(mzero() → A)

  plus(f::(A → B), g::(A → B))::(A → B) ⊣ (A::Ob, B::Ob)
  adjoint(f::(A → B))::(B → A) ⊣ (A::Ob, B::Ob)

  scalar(A::Ob, c::Number)::(A → A)
  antipode(A::Ob)::(A → A)

  # Axioms
  antipode(A) == scalar(A, -1) ⊣ (A::Ob)

  Δ(A) == Δ(A) ⋅ σ(A,A) ⊣ (A::Ob)
  Δ(A) ⋅ (Δ(A) ⊕ id(A)) == Δ(A) ⋅ (id(A) ⊕ Δ(A)) ⊣ (A::Ob)
  Δ(A) ⋅ (◊(A) ⊕ id(A)) == id(A) ⊣ (A::Ob)
  plus(A) == σ(A,A) ⋅ plus(A) ⊣ (A::Ob)
  (plus(A) ⊕ id(A)) ⋅ plus(A) == (id(A) ⊕ plus(A)) ⋅ plus(A) ⊣ (A::Ob)
  (zero(A) ⊕ id(A)) ⋅ plus(A) == id(A) ⊣ (A::Ob)
  plus(A) ⋅ Δ(A) == ((Δ(A) ⊕ Δ(A)) ⋅ (id(A) ⊕ (σ(A, A) ⊕ id(A)))) ⋅ (plus(A) ⊕ plus(A)) ⊣ (A::Ob)
  plus(A) ⋅ ◊(A) == ◊(A) ⊕ ◊(A) ⊣ (A::Ob)
  zero(A) ⋅ Δ(A) == zero(A) ⊕ zero(A) ⊣ (A::Ob)
  zero(A) ⋅ ◊(A) == id(mzero()) ⊣ (A::Ob)
  scalar(A, a) ⋅ scalar(A, b) == scalar(A, a*b) ⊣ (A::Ob, a::Number, b::Number)
  scalar(A, 1) == id(A) ⊣ (A::Ob)
  scalar(A, a) ⋅ Δ(A) == Δ(A) ⋅ (scalar(A, a) ⊕ scalar(A, a)) ⊣ (A::Ob, a::Number)
  scalar(A, a) ⋅ ◊(A) == ◊(A) ⊣ (A::Ob, a::Number)
  (Δ(A) ⋅ (scalar(A, a) ⊕ scalar(A, b))) ⋅ plus(A) == scalar(A, a+b) ⊣ (A::Ob, a::Number, b::Number)
  scalar(A, 0) == ◊(A) ⋅ zero(A) ⊣ (A::Ob)
  zero(A) ⋅ scalar(A, a) == zero(A) ⊣ (A::Ob, a::Number)

  plus(A) ⋅ f == (f ⊕ f) ⋅ plus(B) ⊣ (A::Ob, B::Ob, f::(A → B))
  scalar(A, c) ⋅ f == f ⋅ scalar(B, c) ⊣ (A::Ob, B::Ob, c::Number, f::(A → B))
end

@syntax FreeLinearFunctions(ObExpr,HomExpr) LinearFunctions begin
  oplus(A::Ob, B::Ob) = associate_unit(new(A,B), mzero)
  oplus(f::Hom, g::Hom) = associate(new(f,g))
  compose(f::Hom, g::Hom) = new(f,g; strict=true) # No normalization!
end

""" Doctrine of *linear relations*

The full relational language of graphical linear algebra. This is an abelian
bicategory of relations (`AbelianBicategoryRelations`), written additively.
"""
@signature LinearFunctions(Ob,Hom) => LinearRelations(Ob,Hom) begin
  # Dagger category.
  dagger(f::(A → B))::(A → B) ⊣ (A::Ob, B::Ob)

  # Self-dual compact closed category.
  dunit(A::Ob)::(mzero() → (A ⊕ A))
  dcounit(A::Ob)::((A ⊕ A) → mzero())

  # Merging and creating relations (converses of copying and deleting maps).
  mmerge(A::Ob)::((A ⊕ A) → A)
  @op (∇) := mmerge
  create(A::Ob)::(mzero() → A)
  @op (□) := create

  # Co-addition and co-zero relations (converses of addition and zero maps)
  coplus(A::Ob)::(A → (A ⊕ A))
  cozero(A::Ob)::(A → mzero())

  # Lattice of linear relations.
  meet(f::(A → B), g::(A → B))::(A → B) ⊣ (A::Ob, B::Ob)
  top(A::Ob, B::Ob)::(A → B)
  join(f::(A → B), g::(A → B))::(A → B) ⊣ (A::Ob, B::Ob)
  bottom(A::Ob, B::Ob)::(A → B)
end

@syntax FreeLinearRelations(ObExpr,HomExpr) LinearRelations begin
  oplus(A::Ob, B::Ob) = associate_unit(new(A,B), mzero)
  oplus(f::Hom, g::Hom) = associate(new(f,g))
  compose(f::Hom, g::Hom) = new(f,g; strict=true) # No normalization!
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
  braid(V::LinearOpDom, W::LinearOpDom) =
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
