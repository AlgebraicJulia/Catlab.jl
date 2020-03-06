module GraphicalLinearAlgebra
export LinearFunctions, FreeLinearFunctions, LinearRelations,
  FreeLinearRelations, LinearMapDom, LinearMap,
  Ob, Hom, dom, codom, compose, ⋅, ∘, id, oplus, ⊕, ozero, braid,
  dagger, dunit, docunit, mcopy, Δ, delete, ◊, mmerge, ∇, create, □,
  mplus, ⊞, mzero, coplus, cozero, plus, meet, top, join, bottom,
  scalar, antipode, ⊟, adjoint, evaluate

import Base: +
using AutoHashEquals
using LinearMaps
import LinearMaps: adjoint
const LMs = LinearMaps

using ...Catlab, ...Doctrines
import ...Doctrines:
  Ob, Hom, dom, codom, compose, ⋅, ∘, id, oplus, ⊕, ozero, braid,
  dagger, dunit, dcounit, mcopy, Δ, delete, ◊, mmerge, ∇, create, □,
  mplus, mzero, coplus, cozero, meet, top, join, bottom
using ...Programs
import ...Programs: evaluate_hom

# Doctrines
###########

""" Doctrine of *linear functions*, aka linear maps

Functional fragment of graphical linear algebra.
"""
@signature AdditiveSymmetricMonoidalCategory(Ob,Hom) => LinearFunctions(Ob,Hom) begin
  # Copying and deleting maps.
  mcopy(A::Ob)::Hom(A,oplus(A,A))
  delete(A::Ob)::Hom(A,ozero())

  # Addition and zero maps.
  mplus(A::Ob)::Hom(oplus(A,A),A)
  mzero(A::Ob)::Hom(ozero(),A)

  plus(f::Hom(A,B), g::Hom(A,B))::Hom(A,B) <= (A::Ob, B::Ob)
  # FIXME: Conflicts with LinearMap's definitin of `+`. Need to fix!
  # @op plus :+

  scalar(A::Ob, c::Number)::Hom(A,A)
  antipode(A::Ob)::Hom(A,A) # == scalar(A, -1)

  adjoint(f::Hom(A,B))::Hom(A,B) <= (A::Ob, B::Ob)

  # Unicode syntax
  Δ(A::Ob) = mcopy(A)
  ◇(A::Ob) = delete(A)
  ⊞(A::Ob) = mplus(A)
  ⊟(A::Ob) = antipode(A)
end

@syntax FreeLinearFunctions(ObExpr,HomExpr) LinearFunctions begin
  oplus(A::Ob, B::Ob) = associate_unit(new(A,B), ozero)
  oplus(f::Hom, g::Hom) = associate(new(f,g))
  compose(f::Hom, g::Hom) = new(f,g; strict=true) # No normalization!
end

+(f::FreeLinearFunctions.Hom, g::FreeLinearFunctions.Hom) = plus(f,g)

""" Doctrine of *linear relations*

The full relational language of graphical linear algebra. This is an abelian
bicategory of relations (`AbelianBicategoryRelations`), written additively.
"""
@signature LinearFunctions(Ob,Hom) => LinearRelations(Ob,Hom) begin
  # Dagger category.
  dagger(f::Hom(A,B))::Hom(A,B) <= (A::Ob, B::Ob)

  # Self-dual compact closed category.
  dunit(A::Ob)::Hom(ozero(), oplus(A,A))
  dcounit(A::Ob)::Hom(oplus(A,A), ozero())

  # Merging and creating relations (converses of copying and deleting maps).
  mmerge(A::Ob)::Hom(oplus(A,A),A)
  create(A::Ob)::Hom(ozero(),A)

  # Co-addition and co-zero relations (converses of addition and zero maps)
  coplus(A::Ob)::Hom(A,oplus(A,A))
  cozero(A::Ob)::Hom(A,ozero())

  # Lattice of linear relations.
  meet(f::Hom(A,B), g::Hom(A,B))::Hom(A,B) <= (A::Ob, B::Ob)
  top(A::Ob, B::Ob)::Hom(A,B)
  join(f::Hom(A,B), g::Hom(A,B))::Hom(A,B) <= (A::Ob, B::Ob)
  bottom(A::Ob, B::Ob)::Hom(A,B)

  # Unicode syntax
  ∇(A::Ob) = mmerge(A)
  □(A::Ob) = create(A)
end

@syntax FreeLinearRelations(ObExpr,HomExpr) LinearRelations begin
  oplus(A::Ob, B::Ob) = associate_unit(new(A,B), ozero)
  oplus(f::Hom, g::Hom) = associate(new(f,g))
  compose(f::Hom, g::Hom) = new(f,g; strict=true) # No normalization!
end

+(f::FreeLinearRelations.Hom, g::FreeLinearRelations.Hom) = plus(f,g)

# Evaluation
############

# LinearMaps instance
#--------------------

@auto_hash_equals struct LinearMapDom
  N::Int
end

@instance LinearFunctions(LinearMapDom, LinearMap) begin
  dom(f::LinearMap) = LinearMapDom(size(f,2))
  codom(f::LinearMap) = LinearMapDom(size(f,1))

  compose(f::LinearMap, g::LinearMap) = g*f
  id(V::LinearMapDom) = LMs.UniformScalingMap(1, V.N)

  oplus(V::LinearMapDom, W::LinearMapDom) = LinearMapDom(V.N + W.N)
  oplus(f::LinearMap, g::LinearMap) = LMs.BlockDiagonalMap(f, g)
  ozero(::Type{LinearMapDom}) = LinearMapDom(0)
  braid(V::LinearMapDom, W::LinearMapDom) =
    LinearMap(braid_lm(V.N), braid_lm(W.N), W.N+V.N, V.N+W.N)

  mcopy(V::LinearMapDom) = LinearMap(mcopy_lm, mplus_lm, 2*V.N, V.N)
  delete(V::LinearMapDom) = LinearMap(delete_lm, mzero_lm(V.N), 0, V.N)
  mplus(V::LinearMapDom) = LinearMap(mplus_lm, mcopy_lm, V.N, 2*V.N)
  mzero(V::LinearMapDom) = LinearMap(mzero_lm(V.N), delete_lm, V.N, 0)

  plus(f::LinearMap, g::LinearMap) = f+g
  scalar(V::LinearMapDom, c::Number) = LMs.UniformScalingMap(c, V.N)
  antipode(V::LinearMapDom) = LMs.UniformScalingMap(-1, V.N)
  
  # FIXME: Already defined by LinearMaps.
  #adjoint(f::LinearMap) = LMs.AdjointMap(f)
end

braid_lm(n::Int) = x::AbstractVector -> vcat(x[n+1:end], x[1:n])
mcopy_lm(x::AbstractVector) = vcat(x, x)
delete_lm(x::AbstractVector) = eltype(x)[]
mplus_lm(x::AbstractVector) = begin
  n = length(x) ÷ 2
  x[1:n] + x[n+1:end]
end
mzero_lm(n::Int) = x::AbstractVector -> zeros(eltype(x), n)

# Catlab evaluate
#----------------

function evaluate_hom(f::FreeLinearFunctions.Hom{:generator}, xs::Vector;
                      generators::AbstractDict=Dict())
  M = generators[f]
  x = reduce(vcat, xs; init=eltype(M)[])
  [ M*x ]
end

function evaluate_hom(f::FreeLinearFunctions.Hom{:mplus}, xs::Vector; kw...)
  [ reduce(+, xs) ]
end
function evaluate_hom(f::FreeLinearFunctions.Hom{:mzero}, xs::Vector;
                      generators::AbstractDict=Dict())
  map(collect(codom(f))) do A
    dims = generators[A]
    zeros(dims...)
  end
end

function evaluate_hom(f::FreeLinearFunctions.Hom{:plus}, xs::Vector; kw...)
  mapreduce(+, args(f)) do g
    evaluate_hom(g, xs; kw...)
  end
end

evaluate_hom(f::FreeLinearFunctions.Hom{:scalar}, xs::Vector; kw...) = last(f) .* xs
evaluate_hom(f::FreeLinearFunctions.Hom{:antipode}, xs::Vector; kw...) = -1 .* xs

end
