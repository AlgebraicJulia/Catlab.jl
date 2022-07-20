export ThBicategoryRelations, FreeBicategoryRelations,
  ThAbelianBicategoryRelations, FreeAbelianBicategoryRelations,
  ThDistributiveBicategoryRelations,
  meet, join, top, bottom, plus, zero, coplus, cozero

import Base: join, zero

# Bicategory of relations
#########################

""" Theory of *bicategories of relations*

TODO: The 2-morphisms are missing.

References:

- Carboni & Walters, 1987, "Cartesian bicategories I"
- Walters, 2009, blog post, "Categorical algebras of relations",
  http://rfcwalters.blogspot.com/2009/10/categorical-algebras-of-relations.html
"""
@signature ThBicategoryRelations{Ob,Hom} <: ThHypergraphCategory{Ob,Hom} begin
  # Logical operations.
  meet(R::(A → B), S::(A → B))::(A → B) ⊣ (A::Ob, B::Ob)
  top(A::Ob, B::Ob)::(A → B)
end

@syntax FreeBicategoryRelations{ObExpr,HomExpr} ThBicategoryRelations begin
  otimes(A::Ob, B::Ob) = associate_unit(new(A,B), munit)
  otimes(R::Hom, S::Hom) = associate(new(R,S))
  compose(R::Hom, S::Hom) = associate_unit(new(R,S; strict=true), id)
  dagger(R::Hom) = distribute_unary(distribute_dagger(involute(new(R))),
                                    dagger, otimes)
  meet(R::Hom, S::Hom) = compose(mcopy(dom(R)), otimes(R,S), mmerge(codom(R)))
  top(A::Ob, B::Ob) = compose(delete(A), create(B))
end

""" Theory of *abelian bicategories of relations*

Unlike [`ThBicategoryRelations`](@ref), this theory uses additive notation.

References:

- Carboni & Walters, 1987, "Cartesian bicategories I", Sec. 5
- Baez & Erbele, 2015, "Categories in control"
"""
@signature ThAbelianBicategoryRelations{Ob,Hom} <: ThHypergraphCategoryAdditive{Ob,Hom} begin
  # Second supply of Frobenius monoids.
  plus(A::Ob)::((A ⊕ A) → A)
  zero(A::Ob)::(mzero() → A)
  coplus(A::Ob)::(A → (A ⊕ A))
  cozero(A::Ob)::(A → mzero())

  # Logical operations.
  meet(R::(A → B), S::(A → B))::(A → B) ⊣ (A::Ob, B::Ob)
  top(A::Ob, B::Ob)::(A → B)
  join(R::(A → B), S::(A → B))::(A → B) ⊣ (A::Ob, B::Ob)
  bottom(A::Ob, B::Ob)::(A → B)
end

@syntax FreeAbelianBicategoryRelations{ObExpr,HomExpr} ThAbelianBicategoryRelations begin
  oplus(A::Ob, B::Ob) = associate_unit(new(A,B), mzero)
  oplus(R::Hom, S::Hom) = associate(new(R,S))
  compose(R::Hom, S::Hom) = associate_unit(new(R,S; strict=true), id)
  dagger(R::Hom) = distribute_unary(distribute_dagger(involute(new(R))),
                                    dagger, oplus)
  meet(R::Hom, S::Hom) = compose(mcopy(dom(R)), oplus(R,S), mmerge(codom(R)))
  join(R::Hom, S::Hom) = compose(coplus(dom(R)), oplus(R,S), plus(codom(R)))
  top(A::Ob, B::Ob) = compose(delete(A), create(B))
  bottom(A::Ob, B::Ob) = compose(cozero(A), zero(B))
end

""" Theory of a *distributive bicategory of relations*

References:
  - Carboni & Walters, 1987, "Cartesian bicategories I", Remark 3.7 (mention
    in passing only)
  - Patterson, 2017, "Knowledge representation in bicategories of relations",
    Section 9.2

FIXME: Should also inherit `ThBicategoryOfRelations`, but multiple inheritance is
not yet supported.
"""
@signature ThDistributiveBicategoryRelations{Ob,Hom} <:
    ThDistributiveMonoidalCategoryWithDiagonals{Ob,Hom} begin
  # Self-dual dagger compact category.
  dagger(R::(A → B))::(B → A) ⊣ (A::Ob, B::Ob)
  dunit(A::Ob)::(munit() → (A ⊗ A))
  dcounit(A::Ob)::((A ⊗ A) → munit())
  
  # Merging and creating (right adjoints of copying and deleting maps).
  mmerge(A::Ob)::((A ⊗ A) → A)
  @op (∇) := mmerge
  create(A::Ob)::(munit() → A)
  @op (□) := create

  # Co-addition and co-zero (right adjoints of addition and zero maps).
  coplus(A::Ob)::(A → (A ⊕ A))
  cozero(A::Ob)::(A → mzero())
  
  # The coproduct is automatically a biproduct, due to compact closed structure.
  pair(R::(A → B), S::(A → C))::(A → (B ⊕ C)) ⊣ (A::Ob, B::Ob, C::Ob)
  proj1(A::Ob, B::Ob)::((A ⊕ B) → A)
  proj2(A::Ob, B::Ob)::((A ⊕ B) → B)
  
  # Logical operations.
  meet(R::(A → B), S::(A → B))::(A → B) ⊣ (A::Ob, B::Ob)
  top(A::Ob, B::Ob)::(A → B)
  join(R::(A → B), S::(A → B))::(A → B) ⊣ (A::Ob, B::Ob)
  bottom(A::Ob, B::Ob)::(A → B)
end
