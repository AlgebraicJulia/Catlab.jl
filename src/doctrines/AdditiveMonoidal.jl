export AdditiveMonoidalCategory, oplus, ⊕, mzero,
  AdditiveSymmetricMonoidalCategory, FreeAdditiveSymmetricMonoidalCategory,
  MonoidalCategoryWithCodiagonals, CocartesianCategory, FreeCocartesianCategory,
  mmerge, create, copair, incl1, incl2, ∇, □, braid, σ

import Base: collect, ndims

# Monoidal category
###################

""" Doctrine of *monoidal category* in additive notation

The same as `MonoidalCategory` mathematically but with different notation.
"""
@signature Category(Ob,Hom) => AdditiveMonoidalCategory(Ob,Hom) begin
  oplus(A::Ob, B::Ob)::Ob
  oplus(f::Hom(A,B), g::Hom(C,D))::Hom(oplus(A,C),oplus(B,D)) <=
    (A::Ob, B::Ob, C::Ob, D::Ob)
    @op (⊕) := oplus
  mzero()::Ob
end

# Convenience constructors
oplus(xs::Vector{T}) where T = isempty(xs) ? mzero(T) : foldl(oplus, xs)
oplus(x, y, z, xs...) = oplus([x, y, z, xs...])

# Overload `collect` and `ndims` as for multiplicative monoidal categories.
collect(expr::ObExpr{:oplus}) = vcat(map(collect, args(expr))...)
collect(expr::ObExpr{:mzero}) = roottypeof(expr)[]
ndims(expr::ObExpr{:oplus}) = sum(map(ndims, args(expr)))
ndims(expr::ObExpr{:mzero}) = 0

function show_unicode(io::IO, expr::Union{ObExpr{:oplus},HomExpr{:oplus}}; kw...)
  Syntax.show_unicode_infix(io, expr, "⊕"; kw...)
end
show_unicode(io::IO, expr::ObExpr{:mzero}; kw...) = print(io, "O")

function show_latex(io::IO, expr::Union{ObExpr{:oplus},HomExpr{:oplus}}; kw...)
  Syntax.show_latex_infix(io, expr, "\\oplus"; kw...)
end
show_latex(io::IO, expr::ObExpr{:mzero}; kw...) = print(io, "O")

# Symmetric monoidal category
#############################

""" Doctrine of *symmetric monoidal category* in additive notation

The same as `SymmetricMonoidalCategory` mathematically but with different
notation.
"""
@signature AdditiveMonoidalCategory(Ob,Hom) => AdditiveSymmetricMonoidalCategory(Ob,Hom) begin
  braid(A::Ob, B::Ob)::Hom(oplus(A,B),oplus(B,A))
  @op (σ) := braid
end

@syntax FreeAdditiveSymmetricMonoidalCategory(ObExpr,HomExpr) AdditiveSymmetricMonoidalCategory begin
  oplus(A::Ob, B::Ob) = associate_unit(new(A,B), mzero)
  oplus(f::Hom, g::Hom) = associate(new(f,g))
  compose(f::Hom, g::Hom) = associate(new(f,g; strict=true))
end

# Cocartesian category
######################

""" Doctrine of *monoidal category with codiagonals*

A monoidal category with codiagonals is a symmetric monoidal category equipped
with coherent collections of merging and creating morphisms (monoids).
Unlike in a cocartesian category, the naturality axioms need not be satisfied.

For references, see `MonoidalCategoryWithDiagonals`.
"""
@signature AdditiveSymmetricMonoidalCategory(Ob,Hom) => MonoidalCategoryWithCodiagonals(Ob,Hom) begin
  mmerge(A::Ob)::Hom(oplus(A,A),A)
  @op (∇) := mmerge
  create(A::Ob)::Hom(mzero(),A)
  @op (□) := create
end

""" Doctrine of *cocartesian category*

Actually, this is a cocartesian *symmetric monoidal* category but we omit these
qualifiers for brevity.
"""
@signature MonoidalCategoryWithCodiagonals(Ob,Hom) => CocartesianCategory(Ob,Hom) begin
  copair(f::Hom(A,C), g::Hom(B,C))::Hom(oplus(A,B),C) <= (A::Ob, B::Ob, C::Ob)
  incl1(A::Ob, B::Ob)::Hom(A,oplus(A,B))
  incl2(A::Ob, B::Ob)::Hom(B,oplus(A,B))
end

""" Syntax for a free cocartesian category.

In this syntax, the copairing and inclusion operations are defined using
merging and creation, and do not have their own syntactic elements.
Of course, this convention could be reversed.
"""
@syntax FreeCocartesianCategory(ObExpr,HomExpr) CocartesianCategory begin
  oplus(A::Ob, B::Ob) = associate_unit(new(A,B), mzero)
  oplus(f::Hom, g::Hom) = associate(new(f,g))
  compose(f::Hom, g::Hom) = associate(new(f,g; strict=true))

  copair(f::Hom, g::Hom) = compose(oplus(f,g), mmerge(codom(f)))
  incl1(A::Ob, B::Ob) = oplus(id(A), create(B))
  incl2(A::Ob, B::Ob) = oplus(create(A), id(B))
end

function show_latex(io::IO, expr::HomExpr{:mmerge}; kw...)
  Syntax.show_latex_script(io, expr, "\\nabla")
end
function show_latex(io::IO, expr::HomExpr{:create}; kw...)
  Syntax.show_latex_script(io, expr, "\\square")
end
