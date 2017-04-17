import Lazy: @>

using ..GAT, ..Syntax, ..Rewrite
import ..Syntax: show_unicode, show_latex

""" Doctrine of *bicategory of relations*

TODO: The 2-morphisms are missing. I haven't decided how to handle them yet.

References:

- (Carboni & Walters, 1987, "Cartesian bicategories I")
- (Walters, 2009, blog post, "Categorical algebras of relations",
   http://rfcwalters.blogspot.com/2009/10/categorical-algebras-of-relations.html)
"""
@signature SymmetricMonoidalCategory(Ob,Hom) => BicategoryRelations(Ob,Hom) begin
  # Dagger category.
  dagger(f::Hom(A,B))::Hom(B,A) <= (A::Ob,B::Ob)
  
  # Self-dual compact closed category.
  ev(A::Ob)::Hom(otimes(A,A), munit())
  coev(A::Ob)::Hom(munit(), otimes(A,A))
  
  # Diagonal and codiagonal.
  mcopy(A::Ob)::Hom(A,otimes(A,A))
  delete(A::Ob)::Hom(A,munit())
  mmerge(A::Ob)::Hom(otimes(A,A),A)
  create(A::Ob)::Hom(munit(),A)
end

@syntax FreeBicategoryRelations(ObExpr,HomExpr) BicategoryRelations begin
  otimes(A::Ob, B::Ob) = associate_unit(Super.otimes(A,B), munit)
  otimes(f::Hom, g::Hom) = associate(Super.otimes(f,g))
  compose(f::Hom, g::Hom) = associate(Super.compose(f,g; strict=true))
  dagger(f::Hom) = @>(Super.dagger(f),
    anti_involute(dagger, compose, id),
    distribute_unary(dagger, otimes))
end

""" Doctrine of *abelian bicategory of relations*

Unlike Carboni & Walters, we use additive notation and nomenclature.

References:

- (Carboni & Walters, 1987, "Cartesian bicategories I", Sec. 5)
- (Baez & Erbele, 2015, "Categories in control")
"""
@signature BicategoryRelations(Ob,Hom) => AbelianBicategoryRelations(Ob,Hom) begin
  # Second diagonal and codiagonal.
  plus(A::Ob)::Hom(otimes(A,A),A)
  zero(A::Ob)::Hom(munit(),A)
  coplus(A::Ob)::Hom(A,otimes(A,A))
  cozero(A::Ob)::Hom(A,munit())
end

@syntax FreeAbelianBicategoryRelations(ObExpr,HomExpr) AbelianBicategoryRelations begin
  otimes(A::Ob, B::Ob) = associate_unit(Super.otimes(A,B), munit)
  otimes(f::Hom, g::Hom) = associate(Super.otimes(f,g))
  compose(f::Hom, g::Hom) = associate(Super.compose(f,g; strict=true))
  dagger(f::Hom) = @>(Super.dagger(f),
    anti_involute(dagger, compose, id),
    distribute_unary(dagger, otimes))
end

function show_latex(io::IO, expr::FreeAbelianBicategoryRelations.Ob{:otimes}; kw...)
  show_latex_infix(io, expr, "\\oplus"; kw...)
end
function show_latex(io::IO, expr::FreeAbelianBicategoryRelations.Hom{:otimes}; kw...)
  show_latex_infix(io, expr, "\\oplus"; kw...)
end
show_latex(io::IO, expr::FreeAbelianBicategoryRelations.Ob{:munit}; kw...) = print(io, "O")

function show_latex(io::IO, expr::FreeAbelianBicategoryRelations.Hom{:plus}; kw...)
  show_latex_script(io, expr, "\\blacktriangledown")
end
function show_latex(io::IO, expr::FreeAbelianBicategoryRelations.Hom{:coplus}; kw...)
  show_latex_script(io, expr, "\\blacktriangle")
end
function show_latex(io::IO, expr::FreeAbelianBicategoryRelations.Hom{:zero}; kw...)
  show_latex_script(io, expr, "\\blacksquare")
end
function show_latex(io::IO, expr::FreeAbelianBicategoryRelations.Hom{:cozero}; kw...)
  show_latex_script(io, expr, "\\blacklozenge")
end
