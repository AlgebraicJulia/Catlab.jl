export BicategoryRelations, FreeBicategoryRelations,
  AbelianBicategoryRelations, FreeAbelianBicategoryRelations,
  meet, join, top, bottom, plus, zero, coplus, cozero

import Base: join, zero

# Bicategory of relations
#########################

""" Doctrine of *bicategory of relations*

TODO: The 2-morphisms are missing. I haven't decided how to handle them yet.

References:

- Carboni & Walters, 1987, "Cartesian bicategories I"
- Walters, 2009, blog post, "Categorical algebras of relations",
  http://rfcwalters.blogspot.com/2009/10/categorical-algebras-of-relations.html
"""
@signature MonoidalCategoryWithBidiagonals(Ob,Hom) => BicategoryRelations(Ob,Hom) begin
  # Dagger category.
  dagger(f::(A → B))::(B → A) ⊣ (A::Ob,B::Ob)

  # Self-dual compact closed category.
  dunit(A::Ob)::(munit() → (A ⊗ A))
  dcounit(A::Ob)::((A ⊗ A) → munit())

  # Logical operations.
  meet(f::(A → B), g::(A → B))::(A → B) ⊣ (A::Ob, B::Ob)
  top(A::Ob, B::Ob)::(A → B)
end

@syntax FreeBicategoryRelations(ObExpr,HomExpr) BicategoryRelations begin
  otimes(A::Ob, B::Ob) = associate_unit(new(A,B), munit)
  otimes(f::Hom, g::Hom) = associate(new(f,g))
  compose(f::Hom, g::Hom) = associate(new(f,g; strict=true))
  dagger(f::Hom) = distribute_unary(distribute_dagger(involute(new(f))),
                                    dagger, otimes)
  meet(f::Hom, g::Hom) = compose(mcopy(dom(f)), otimes(f,g), mmerge(codom(f)))
  top(A::Ob, B::Ob) = compose(delete(A), create(B))
end

""" Doctrine of *abelian bicategory of relations*

Unlike Carboni & Walters, we use additive notation and nomenclature.

References:

- Carboni & Walters, 1987, "Cartesian bicategories I", Sec. 5
- Baez & Erbele, 2015, "Categories in control"
"""
@signature BicategoryRelations(Ob,Hom) => AbelianBicategoryRelations(Ob,Hom) begin
  # Second diagonal and codiagonal.
  plus(A::Ob)::((A ⊗ A) → A)
  zero(A::Ob)::(munit() → A)
  coplus(A::Ob)::(A → (A ⊗ A))
  cozero(A::Ob)::(A → munit())

  # Logical operations.
  join(f::(A → B), g::(A → B))::(A → B) ⊣ (A::Ob, B::Ob)
  bottom(A::Ob, B::Ob)::(A → B)
end

@syntax FreeAbelianBicategoryRelations(ObExpr,HomExpr) AbelianBicategoryRelations begin
  otimes(A::Ob, B::Ob) = associate_unit(new(A,B), munit)
  otimes(f::Hom, g::Hom) = associate(new(f,g))
  compose(f::Hom, g::Hom) = associate(new(f,g; strict=true))
  dagger(f::Hom) = distribute_unary(distribute_dagger(involute(new(f))),
                                    dagger, otimes)
  meet(f::Hom, g::Hom) = compose(mcopy(dom(f)), otimes(f,g), mmerge(codom(f)))
  join(f::Hom, g::Hom) = compose(coplus(dom(f)), otimes(f,g), plus(codom(f)))
  top(A::Ob, B::Ob) = compose(delete(A), create(B))
  bottom(A::Ob, B::Ob) = compose(cozero(A), zero(B))
end

function show_latex(io::IO, expr::HomExpr{:plus}; kw...)
  Syntax.show_latex_script(io, expr, "\\blacktriangledown")
end
function show_latex(io::IO, expr::HomExpr{:coplus}; kw...)
  Syntax.show_latex_script(io, expr, "\\blacktriangle")
end
function show_latex(io::IO, expr::HomExpr{:zero}; kw...)
  Syntax.show_latex_script(io, expr, "\\blacksquare")
end
function show_latex(io::IO, expr::HomExpr{:cozero}; kw...)
  Syntax.show_latex_script(io, expr, "\\blacklozenge")
end
