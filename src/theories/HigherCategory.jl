export ThCategory2, FreeCategory2, Hom2, Hom2Expr, composeH, *,
  ThDoubleCategory, FreeDoubleCategory, Pro, Cell, ProExpr, CellExpr,
  dom, codom, src, tgt, pcompose, pid,
  ThMonoidalDoubleCategory, ThSymmetricMonoidalDoubleCategory,
  FreeSymmetricMonoidalDoubleCategory

import Base: *

abstract type Hom2Expr{T} <: CategoryExpr{T} end
abstract type ArrExpr{T} <: CategoryExpr{T} end
abstract type ProExpr{T} <: CategoryExpr{T} end
abstract type CellExpr{T} <: CategoryExpr{T} end

# 2-category
############

""" Theory of *2-categories*
"""
@signature ThCategory2{Ob,Hom,Hom2} <: ThCategory{Ob,Hom} begin
  """ 2-morphism in a 2-category """
  Hom2(dom::Hom(A,B), codom::Hom(A,B))::TYPE ⊣ (A::Ob, B::Ob)
  @op begin
    (⇒) := Hom2
    (*) := composeH
  end

  # Hom categories: vertical composition
  id(f)::(f ⇒ f) ⊣ (A::Ob, B::Ob, f::(A → B))
  compose(α::(f ⇒ g), β::(g ⇒ h))::(f ⇒ h) ⊣
    (A::Ob, B::Ob, f::(A → B), g::(A → B), h::(A → B))

  # Horizontal composition, including whiskering
  composeH(α::(f ⇒ g), β::(h ⇒ k))::((f ⋅ h) ⇒ (g ⋅ k)) ⊣
    (A::Ob, B::Ob, C::Ob, f::(A → B), g::(A → B), h::(B → C), k::(B → C))
  composeH(α::(f ⇒ g), h::(B → C))::((f ⋅ h) ⇒ (g ⋅ h)) ⊣
    (A::Ob, B::Ob, C::Ob, f::(A → B), g::(A → B))
  composeH(f::(A → B), β::(g ⇒ h))::((f ⋅ g) ⇒ (f ⋅ h)) ⊣
    (A::Ob, B::Ob, C::Ob, g::(B → C), h::(B → C))
end

# Convenience constructors
composeH(αs::AbstractVector) = foldl(composeH, αs)
composeH(α, β, γ, αs...) = composeH([α, β, γ, αs...])

""" Syntax for a 2-category.

This syntax checks domains of morphisms but not 2-morphisms.
"""
@syntax FreeCategory2{ObExpr,HomExpr,Hom2Expr} ThCategory2 begin
  compose(f::Hom, g::Hom) = associate_unit(new(f,g; strict=true), id)
  compose(α::Hom2, β::Hom2) = associate_unit(new(α,β), id)
  composeH(α::Hom2, β::Hom2) = associate(new(α,β))
  composeH(α::Hom2, h::Hom) = composeH(α, id(h))
  composeH(f::Hom, β::Hom2) = composeH(id(f), β)
end

show_unicode(io::IO, expr::CategoryExpr{:composeH}; kw...) =
  Syntax.show_unicode_infix(io, expr, "*"; kw...)

show_latex(io::IO, expr::CategoryExpr{:composeH}; kw...) =
  Syntax.show_latex_infix(io, expr, "*"; kw...)

# Double category
#################

""" Theory of *double categories*

A *strict double category* ``𝔻`` is an internal category

``(S,T: 𝔻₁ ⇉ 𝔻₀, U: 𝔻₀ → 𝔻₁, *: 𝔻₁ ×_{𝔻₀} 𝔻₁ → 𝔻₁)``

in **Cat** where

- objects of ``𝔻₀`` are objects of ``𝔻``
- morphisms of ``𝔻₀`` are arrows (vertical morphisms) of ``𝔻``
- objects of ``𝔻₁`` are proarrows (horizontal morphisms) of ``𝔻``
- morphisms of ``D₁`` are cells of ``𝔻``.

The domain and codomain (top and bottom) of a cell are given by the domain and
codomain in ``𝔻₁`` and the source and target (left and right) are given by the
functors ``S,T``.
"""
@theory ThDoubleCategory{Ob,Hom,Pro,Cell} <: ThCategory{Ob,Hom} begin
  """ Proarrow (horizontal morphism) in a double category """
  Pro(src::Ob, tgt::Ob)::TYPE

  """ 2-cell in a double category """
  Cell(dom::Pro(A,B), codom::Pro(C,D),
       src::Hom(A,C), tgt::Hom(B,D))::TYPE ⊣ (A::Ob, B::Ob, C::Ob, D::Ob)

  @op begin
    (↛) := Pro
    (⇒) := Cell
    (*) := pcompose
  end

  # Category 𝔻₁: internal category structure for proarrows and cells.
  compose(α::Cell(m, n, f, g), β::Cell(n, p, h, k))::Cell(m, p, f⋅h, g⋅k) ⊣
    (A::Ob, B::Ob, C::Ob, X::Ob, Y::Ob, Z::Ob,
     f::(A → B), g::(X → Y), h::(B → C), k::(Y → Z),
     m::(A ↛ X), n::(B ↛ Y), p::(C ↛ Z))
  id(m::(A ↛ B))::Cell(m, m, id(A), id(B)) ⊣ (A::Ob, B::Ob)

  # External composition.
  pcompose(m::(A ↛ B), n::(B ↛ C))::(A ↛ C) ⊣ (A::Ob, B::Ob, C::Ob)
  pid(A::Ob)::(A ↛ A) ⊣ (A::Ob)

  pcompose(α::Cell(m, p, f, g), β::Cell(n, q, g, h))::Cell(m*n, p*q, f, h) ⊣
    (A::Ob, B::Ob, C::Ob, X::Ob, Y::Ob, Z::Ob,
     f::(A → X), g::(B → Y), h::(C → Z),
     m::(A ↛ B), n::(B ↛ C), p::(X ↛ Y), q::(Y ↛ Z))
  pid(f::(A → B))::Cell(pid(A), pid(B), f, f) ⊣ (A::Ob, B::Ob)

  # Axioms for external category structure.
  ((m * n) * p == m * (n * p)
    ⊣ (A::Ob, B::Ob, C::Ob, D::Ob, m::(A ↛ B), n::(B ↛ C), p::(C ↛ D)))
  m * pid(B) == m ⊣ (A::Ob, B::Ob, m::(A ↛ B))
  pid(A) * m == m ⊣ (A::Ob, B::Ob, m::(A ↛ B))

  # TODO: Axioms for cells.
end

# Convenience constructors
pcompose(αs::AbstractVector) = foldl(pcompose, αs)
pcompose(α, β, γ, αs...) = pcompose([α, β, γ, αs...])

""" Syntax for a double category.

Checks domains of morphisms but not 2-morphisms.
"""
@syntax FreeDoubleCategory{ObExpr,HomExpr,ProExpr,CellExpr} ThDoubleCategory begin
  compose(f::Hom, g::Hom) = associate_unit(new(f,g; strict=true), id)
  compose(α::Cell, β::Cell) = associate_unit(new(α,β), id)
  pcompose(m::Pro, n::Pro) = associate_unit(new(m,n; strict=true), pid)
  pcompose(α::Cell, β::Cell) = associate_unit(new(α,β), pid)
end

show_unicode(io::IO, expr::CategoryExpr{:pcompose}; kw...) =
  Syntax.show_unicode_infix(io, expr, "*"; kw...)

show_latex(io::IO, expr::CategoryExpr{:pcompose}; kw...) =
  Syntax.show_latex_infix(io, expr, "*"; kw...)

# Monoidal double category
##########################

""" Theory of *monoidal double categories*

To avoid associators and unitors, we assume that the monoidal double category is
fully *strict*: both the double category and its monoidal product are strict.
Apart from assuming strictness, this theory agrees with the definition of a
monoidal double category in (Shulman 2010) and other recent works.

In a monoidal double category ``(𝔻,⊗,I)``, the underlying categories ``𝔻₀`` and
``𝔻₁`` are each monoidal categories, ``(𝔻₀,⊗₀,I₀)`` and ``(𝔻₁,⊗₁,I₁)``, subject
to further axioms such as the source and target functors ``S, T: 𝔻₁ → 𝔻₀`` being
strict monoidal functors.

Despite the apparent asymmetry in this setup, the definition of a monoidal
double category unpacks to be nearly symmetric with respect to arrows and
proarrows, except that the monoidal unit ``I₀`` of ``𝔻₀`` induces the monoidal
unit of ``𝔻₁`` as ``I₁ = U(I₀)``.

References:

- Shulman, 2010: Constructing symmetric monoidal bicategories

FIXME: Should also inherit `ThMonoidalCategory{Ob,Hom}` but multiple inheritance
is not supported.
"""
@theory ThMonoidalDoubleCategory{Ob,Hom,Pro,Cell} <: ThDoubleCategory{Ob,Hom,Pro,Cell} begin
  @op (⊗) := otimes

  # Monoid in 𝔻₀.
  otimes(A::Ob, B::Ob)::Ob
  otimes(f::(A → B), g::(C → D))::((A ⊗ C) → (B ⊗ D)) ⊣ (A::Ob, B::Ob, C::Ob, D::Ob)
  munit()::Ob

  # Monoid axioms for (𝔻₀,⊗₀,I₀).
  (A ⊗ B) ⊗ C == A ⊗ (B ⊗ C) ⊣ (A::Ob, B::Ob, C::Ob)
  A ⊗ munit() == A ⊣ (A::Ob)
  munit() ⊗ A == A ⊣ (A::Ob)
  (f ⊗ g) ⊗ h == f ⊗ (g ⊗ h) ⊣ (A::Ob, B::Ob, C::Ob, X::Ob, Y::Ob, Z::Ob,
                                f::(A → X), g::(B → Y), h::(C → Z))

  # Functorality axioms for (𝔻₀,⊗₀,I₀).
  ((f ⊗ g) ⋅ (h ⊗ k) == (f ⋅ h) ⊗ (g ⋅ k)
    ⊣ (A::Ob, B::Ob, C::Ob, X::Ob, Y::Ob, Z::Ob,
       f::(A → B), h::(B → C), g::(X → Y), k::(Y → Z)))
  id(A ⊗ B) == id(A) ⊗ id(B) ⊣ (A::Ob, B::Ob)

  # Monoid in 𝔻₁.
  otimes(m::(A ↛ B), n::(C ↛ D))::((A ⊗ C) ↛ (B ⊗ D)) ⊣ (A::Ob, B::Ob, C::Ob, D::Ob)
  otimes(α::Cell(m,n,f,g), β::Cell(m′,n′,f′,g′))::Cell(m⊗m′,n⊗n′,f⊗f′,g⊗g′) ⊣
    (A::Ob, B::Ob, C::Ob, D::Ob, A′::Ob, B′::Ob, C′::Ob, D′::Ob,
     f::(A → C), g::(B → D), f′::(A′ → C′), g′::(B′ → D′),
     m::(A ↛ B), n::(C ↛ D), m′::(A′ ↛ B′), n′::(C′ ↛ D′))

  # Monoid axioms for (𝔻₁,⊗₁,I₁).
  (m ⊗ n) ⊗ p == m ⊗ (n ⊗ p) ⊣ (A::Ob, B::Ob, C::Ob, X::Ob, Y::Ob, Z::Ob,
                                m::(A ↛ X), n::(B ↛ Y), p::(C ↛ Z))
  m ⊗ pid(munit()) == m ⊣ (A::Ob, B::Ob, m::(A ↛ B))
  pid(munit()) ⊗ m == m ⊣ (A::Ob, B::Ob, m::(A ↛ B))
  (α ⊗ β) ⊗ γ == α ⊗ (β ⊗ γ) ⊣
    (A₁::Ob, A₂::Ob, A₃::Ob, B₁::Ob, B₂::Ob, B₃::Ob,
     C₁::Ob, C₂::Ob, C₃::Ob, D₁::Ob, D₂::Ob, D₃::Ob,
     f₁::(A₁→C₁), f₂::(A₂→C₂), f₃::(A₃→C₃), g₁::(B₁→D₁), g₂::(B₂→D₂), g₃::(B₃→D₃),
     m₁::(A₁↛B₁), m₂::(A₂↛B₂), m₃::(A₃↛B₃), n₁::(C₁↛D₁), n₂::(C₂↛D₂), n₃::(C₃↛D₃),
     α::Cell(m₁,n₁,f₁,g₁), β::Cell(m₂,n₂,f₂,g₂), γ::Cell(m₃,m₃,f₃,g₃))

  # Functorality axioms for (𝔻₁,⊗₁,I₁).
  ((α ⊗ α′) ⋅ (β ⊗ β′)) == (α ⋅ β) ⊗ (α′ ⋅ β′) ⊣
    (A::Ob, B::Ob, C::Ob, A′::Ob, B′::Ob, C′::Ob,
     X::Ob, Y::Ob, Z::Ob, X′::Ob, Y′::Ob, Z′::Ob,
     f::(A→B), g::(X→Y), f′::(A′→B′), g′::(X′→Y′),
     h::(B→C), k::(Y→Z), h′::(B′→C′), k′::(Y′→Z′),
     m::(A↛X), n::(B↛Y), p::(C↛Z), m′::(A′↛X′), n′::(B′↛Y′), p′::(C′↛Z′),
     α::Cell(m,n,f,g), α′::Cell(m′,n′,f′,g′),
     β::Cell(n,p,h,k), β′::Cell(n′,p′,h′,k′))
  id(m ⊗ n) == id(m) ⊗ id(n) ⊣ (A::Ob, B::Ob, X::Ob, Y::Ob, m::(A ↛ X), n::(B ↛ Y))

  # External functorality of ⊗: 𝔻×𝔻 → 𝔻 and I: 1 → 𝔻.
  # TODO: Interchange of external composition of cells.
  ((m ⊗ n) * (p ⊗ q) == (m * p) ⊗ (n * q)
    ⊣ (A::Ob, B::Ob, C::Ob, X::Ob, Y::Ob, Z::Ob,
       m::(A ↛ B), p::(B ↛ C), n::(X ↛ Y), q::(Y ↛ Z)))
  pid(A ⊗ B) == pid(A) ⊗ pid(B) ⊣ (A::Ob, B::Ob)
end

""" Theory of *symmetric monoidal double categories*

Unlike the classical notion of strict double categories, symmetric monoidal
double categories do not treat the two directions on an equal footing, even when
everything (except the braiding) is strict. See [`MonoidalDoubleCategory`](@ref)
for references.

FIXME: Should also inherit `ThSymmetricMonoidalCategory{Ob,Hom}` but multiple
inheritance is not supported.
"""
@theory ThSymmetricMonoidalDoubleCategory{Ob,Hom,Pro,Cell} <: ThMonoidalDoubleCategory{Ob,Hom,Pro,Cell} begin
  braid(A::Ob, B::Ob)::((A ⊗ B) → (B ⊗ A))
  braid(m::(A ↛ C), n::(B ↛ D))::Cell(m ⊗ n, n ⊗ m, σ(A,B), σ(C,D)) ⊣
    (A::Ob, B::Ob, C::Ob, D::Ob)
  @op (σ) := braid

  # Involutivity axioms.
  σ(A,B) ⋅ σ(B,A) == id(A ⊗ B) ⊣ (A::Ob, B::Ob)
  σ(m,n) ⋅ σ(n,m) == id(m ⊗ n) ⊣ (A::Ob, B::Ob, C::Ob, D::Ob,
                                  m::(A ↛ C), n::(B ↛ D))

  # Naturality axioms.
  (f⊗g) ⋅ σ(C,D) == σ(A,B) ⋅ (g⊗f) ⊣ (A::Ob, B::Ob, C::Ob, D::Ob,
                                      f::(A → C), g::(B → D))
  ((α⊗β) ⋅ σ(m′,n′) == σ(m,n) ⋅ (β⊗α) ⊣
    (A::Ob, B::Ob, C::Ob, D::Ob, A′::Ob, B′::Ob, C′::Ob, D′::Ob,
     f::(A → C), g::(B → D), f′::(A′ → C′), g′::(B′ → D′),
     m::(A ↛ B), n::(C ↛ D), m′::(A′ ↛ B′), n′::(C′ ↛ D′),
     α::Cell(m,n,f,g), β::Cell(m′,n′,f′,g′)))

  # Coherence axioms.
  σ(A,B⊗C) == (σ(A,B) ⊗ id(C)) ⋅ (id(B) ⊗ σ(A,C)) ⊣ (A::Ob, B::Ob, C::Ob)
  σ(A⊗B,C) == (id(A) ⊗ σ(B,C)) ⋅ (σ(A,C) ⊗ id(B)) ⊣ (A::Ob, B::Ob, C::Ob)
  σ(m,n⊗p) == (σ(m,n) ⊗ id(p)) ⋅ (id(n) ⊗ σ(m,p)) ⊣
    (A::Ob, B::Ob, C::Ob, X::Ob, Y::Ob, Z::Ob, m::(A↛X), n::(B↛Y), p::(C↛Z))
  σ(m⊗n,p) == (id(m) ⊗ σ(n,p)) ⋅ (σ(m,p) ⊗ id(n)) ⊣
    (A::Ob, B::Ob, C::Ob, X::Ob, Y::Ob, Z::Ob, m::(A↛X), n::(B↛Y), p::(C↛Z))
end

@syntax FreeSymmetricMonoidalDoubleCategory{ObExpr,HomExpr,ProExpr,CellExpr} ThSymmetricMonoidalDoubleCategory begin
  otimes(A::Ob, B::Ob) = associate_unit(new(A,B), munit)
  otimes(f::Hom, g::Hom) = associate(new(f,g))
  otimes(f::Pro, g::Pro) = associate(new(f,g))
  otimes(f::Cell, g::Cell) = associate(new(f,g))
  compose(f::Hom, g::Hom) = associate_unit(new(f,g; strict=true), id)
  compose(α::Cell, β::Cell) = associate_unit(new(α,β), id)
  pcompose(m::Pro, n::Pro) = associate_unit(new(m,n; strict=true), pid)
  pcompose(α::Cell, β::Cell) = associate_unit(new(α,β), pid)
end

show_unicode(io::IO, expr::CategoryExpr{:pbraid}; kw...) =
  Syntax.show_unicode_infix(io, expr, "σ"; kw...)
show_latex(io::IO, expr::CategoryExpr{:pbraid}; kw...) =
  Syntax.show_latex_script(io, expr, "\\sigma")
