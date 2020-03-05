module GraphicalLinearAlgebra
export LinearMaps, FreeLinearMaps, LinearRelations,
  Ob, Hom, dom, codom, compose, ⋅, ∘, id, oplus, ⊕, ozero, braid,
  dagger, dunit, docunit, mcopy, Δ, delete, ◇, mmerge, ∇, create, □,
  mplus, ⊞, mzero, coplus, cozero, plus, meet, top, join, bottom,
  scalar, antipode, ⊟, adjoint, evaluate

import Base: +
import LinearAlgebra: adjoint

using ...Catlab, ...Doctrines
import ...Doctrines:
  Ob, Hom, dom, codom, compose, ⋅, ∘, id, oplus, ⊕, ozero, braid,
  dagger, dunit, dcounit, mcopy, Δ, delete, ◇, mmerge, ∇, create, □,
  mplus, mzero, coplus, cozero, meet, top, join, bottom
using ...Programs
import ...Programs: evaluate_hom

# Doctrines
###########

""" Doctrine of *linear maps*

Functional fragment of graphical linear algebra.
"""
@signature AdditiveSymmetricMonoidalCategory(Ob,Hom) => LinearMaps(Ob,Hom) begin
  # Copying and deleting maps.
  mcopy(A::Ob)::Hom(A,oplus(A,A))
  delete(A::Ob)::Hom(A,ozero())

  # Addition and zero maps.
  mplus(A::Ob)::Hom(oplus(A,A),A)
  mzero(A::Ob)::Hom(ozero(),A)

  plus(f::Hom(A,B), g::Hom(A,B))::Hom(A,B) <= (A::Ob, B::Ob)

  scalar(A::Ob, c::Number)::Hom(A,A)
  antipode(A::Ob)::Hom(A,A) # == scalar(A, -1)
  adjoint(f::Hom(A,B))::Hom(A,B) <= (A::Ob, B::Ob)

  # Unicode syntax
  Δ(A::Ob) = mcopy(A)
  ◇(A::Ob) = delete(A)
  ⊞(A::Ob) = mplus(A)
  +(f::Hom, g::Hom) = plus(f,g)
  ⊟(A::Ob) = antipode(A)
end

@syntax FreeLinearMaps(ObExpr,HomExpr) LinearMaps begin
  oplus(A::Ob, B::Ob) = associate_unit(new(A,B), ozero)
  oplus(f::Hom, g::Hom) = associate(new(f,g))
  compose(f::Hom, g::Hom) = new(f,g; strict=true) # No normalization!
end

""" Doctrine of *linear relations*

The full relational language of graphical linear algebra. This is an abelian
bicategory of relations (`AbelianBicategoryRelations`), written additively.
"""
@signature LinearMaps(Ob,Hom) => LinearRelations(Ob,Hom) begin
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

# Evaluation
############

function evaluate_hom(f::FreeLinearMaps.Hom{:generator}, xs::Vector;
                      generators::AbstractDict=Dict())
  M = generators[f]
  x = reduce(vcat, xs; init=eltype(M)[])
  [ M*x ]
end

function evaluate_hom(f::FreeLinearMaps.Hom{:mplus}, xs::Vector; kw...)
  [ reduce(+, xs) ]
end
function evaluate_hom(f::FreeLinearMaps.Hom{:mzero}, xs::Vector;
                      generators::AbstractDict=Dict())
  map(collect(codom(f))) do A
    dims = generators[A]
    zeros(dims...)
  end
end

function evaluate_hom(f::FreeLinearMaps.Hom{:plus}, xs::Vector; kw...)
  mapreduce(+, args(f)) do g
    evaluate_hom(g, xs; kw...)
  end
end

evaluate_hom(f::FreeLinearMaps.Hom{:scalar}, xs::Vector; kw...) = last(f) .* xs
evaluate_hom(f::FreeLinearMaps.Hom{:antipode}, xs::Vector; kw...) = -1 .* xs

end
