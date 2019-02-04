export BicategoryRelations, FreeBicategoryRelations,
  AbelianBicategoryRelations, FreeAbelianBicategoryRelations,
  mplus, mzero, coplus, cozero

# Bicategory of relations
#########################

""" Doctrine of *bicategory of relations*

TODO: The 2-morphisms are missing. I haven't decided how to handle them yet.

References:

- Carboni & Walters, 1987, "Cartesian bicategories I"
- Walters, 2009, blog post, "Categorical algebras of relations",
  http://rfcwalters.blogspot.com/2009/10/categorical-algebras-of-relations.html
"""
@signature MonoidalCategoryWithDiagonals(Ob,Hom) => BicategoryRelations(Ob,Hom) begin
  # Dagger category.
  dagger(f::Hom(A,B))::Hom(B,A) <= (A::Ob,B::Ob)
  
  # Self-dual compact closed category.
  dunit(A::Ob)::Hom(munit(), otimes(A,A))
  dcounit(A::Ob)::Hom(otimes(A,A), munit())
end

@syntax FreeBicategoryRelations(ObExpr,HomExpr) BicategoryRelations begin
  otimes(A::Ob, B::Ob) = associate_unit(Super.otimes(A,B), munit)
  otimes(f::Hom, g::Hom) = associate(Super.otimes(f,g))
  compose(f::Hom, g::Hom) = associate(Super.compose(f,g; strict=true))

  function dagger(f::Hom)
    f = anti_involute(Super.dagger(f), dagger, compose, id)
    distribute_unary(f, dagger, otimes)
  end
end

""" Doctrine of *abelian bicategory of relations*

Unlike Carboni & Walters, we use additive notation and nomenclature.

References:

- Carboni & Walters, 1987, "Cartesian bicategories I", Sec. 5
- Baez & Erbele, 2015, "Categories in control"
"""
@signature BicategoryRelations(Ob,Hom) => AbelianBicategoryRelations(Ob,Hom) begin
  # Second diagonal and codiagonal.
  mplus(A::Ob)::Hom(otimes(A,A),A)
  mzero(A::Ob)::Hom(munit(),A)
  coplus(A::Ob)::Hom(A,otimes(A,A))
  cozero(A::Ob)::Hom(A,munit())
end

@syntax FreeAbelianBicategoryRelations(ObExpr,HomExpr) AbelianBicategoryRelations begin
  otimes(A::Ob, B::Ob) = associate_unit(Super.otimes(A,B), munit)
  otimes(f::Hom, g::Hom) = associate(Super.otimes(f,g))
  compose(f::Hom, g::Hom) = associate(Super.compose(f,g; strict=true))
  
  function dagger(f::Hom)
    f = anti_involute(Super.dagger(f), dagger, compose, id)
    distribute_unary(f, dagger, otimes)
  end
end

function show_latex(io::IO, expr::FreeAbelianBicategoryRelations.Ob{:otimes}; kw...)
  Syntax.show_latex_infix(io, expr, "\\oplus"; kw...)
end
function show_latex(io::IO, expr::FreeAbelianBicategoryRelations.Hom{:otimes}; kw...)
  Syntax.show_latex_infix(io, expr, "\\oplus"; kw...)
end
show_latex(io::IO, expr::FreeAbelianBicategoryRelations.Ob{:munit}; kw...) = print(io, "O")

function show_latex(io::IO, expr::FreeAbelianBicategoryRelations.Hom{:mplus}; kw...)
  Syntax.show_latex_script(io, expr, "\\blacktriangledown")
end
function show_latex(io::IO, expr::FreeAbelianBicategoryRelations.Hom{:coplus}; kw...)
  Syntax.show_latex_script(io, expr, "\\blacktriangle")
end
function show_latex(io::IO, expr::FreeAbelianBicategoryRelations.Hom{:mzero}; kw...)
  Syntax.show_latex_script(io, expr, "\\blacksquare")
end
function show_latex(io::IO, expr::FreeAbelianBicategoryRelations.Hom{:cozero}; kw...)
  Syntax.show_latex_script(io, expr, "\\blacklozenge")
end
