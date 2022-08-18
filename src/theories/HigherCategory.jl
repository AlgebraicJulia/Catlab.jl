export ThCategory2, FreeCategory2, Hom2, Hom2Expr, composeH, *,
  ThDoubleCategory, FreeDoubleCategory, Pro, Cell, ProExpr, CellExpr,
  dom, codom, src, tgt, pcompose, pid,
  ThDoubleCategoryWithTabulators, Tab, proarrow,
  tabulator, ob, proj1, proj2, cell, universal,
  ThEquipment, companion, companion_unit, companion_counit,
  conjoint, conjoint_unit, conjoint_counit,
  ThMonoidalDoubleCategory, ThSymmetricMonoidalDoubleCategory,
  FreeSymmetricMonoidalDoubleCategory,
  ThCartesianDoubleCategory

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

A *strict double category* ``D`` is an internal category

``(S,T: D₁ ⇉ D₀, U: D₀ → D₁, *: D₁ ×_{D₀} D₁ → D₁)``

in **Cat** where

- objects of ``D₀`` are objects of ``D``
- morphisms of ``D₀`` are arrows (vertical morphisms) of ``D``
- objects of ``D₁`` are proarrows (horizontal morphisms) of ``D``
- morphisms of ``D₁`` are cells of ``D``.

The domain and codomain (top and bottom) of a cell are given by the domain and
codomain in ``D₁`` and the source and target (left and right) are given by the
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

  # Category D₀: category structure on objects and arrows.
  # Inherited from `ThCategory`.

  # Category D₁: category structure on proarrows and cells.
  compose(α::Cell(m, n, f, g), β::Cell(n, p, h, k))::Cell(m, p, f⋅h, g⋅k) ⊣
    (A::Ob, B::Ob, C::Ob, X::Ob, Y::Ob, Z::Ob,
     m::(A ↛ X), n::(B ↛ Y), p::(C ↛ Z),
     f::(A → B), g::(X → Y), h::(B → C), k::(Y → Z))
  id(m::(A ↛ B))::Cell(m, m, id(A), id(B)) ⊣ (A::Ob, B::Ob)

  (α ⋅ β) ⋅ γ == α ⋅ (β ⋅ γ) ⊣
    (A::Ob, B::Ob, C::Ob, D::Ob, W::Ob, X::Ob, Y::Ob, Z::Ob,
     m::(A↛W), n::(B↛X), p::(C↛Y), q::(D↛Z),
     f::(A→B), g::(B→C), h::(C→D), i::(W→X), j::(X→Y), k::(Y→Z),
     α::Cell(m,n,f,i), β::Cell(n,p,g,j), γ::Cell(p,q,h,k))
  α ⋅ id(n) == α ⊣ (A::Ob, B::Ob, C::Ob, D::Ob, m::(A↛B), n::(C↛D),
                    f::(A→C), g::(B→D), α::Cell(m,n,f,g))
  id(m) ⋅ α == α ⊣ (A::Ob, B::Ob, C::Ob, D::Ob, m::(A↛B), n::(C↛D),
                    f::(A→C), g::(B→D), α::Cell(m,n,f,g))

  # External category operations.
  pcompose(m::(A ↛ B), n::(B ↛ C))::(A ↛ C) ⊣ (A::Ob, B::Ob, C::Ob)
  pid(A::Ob)::(A ↛ A) ⊣ (A::Ob)

  pcompose(α::Cell(m, p, f, g), β::Cell(n, q, g, h))::Cell(m*n, p*q, f, h) ⊣
    (A::Ob, B::Ob, C::Ob, X::Ob, Y::Ob, Z::Ob,
     m::(A ↛ B), n::(B ↛ C), p::(X ↛ Y), q::(Y ↛ Z),
     f::(A → X), g::(B → Y), h::(C → Z))
  pid(f::(A → B))::Cell(pid(A), pid(B), f, f) ⊣ (A::Ob, B::Ob)

  # External category axioms.
  (m * n) * p == m * (n * p) ⊣
    (A::Ob, B::Ob, C::Ob, D::Ob, m::(A ↛ B), n::(B ↛ C), p::(C ↛ D))
  m * pid(B) == m ⊣ (A::Ob, B::Ob, m::(A ↛ B))
  pid(A) * m == m ⊣ (A::Ob, B::Ob, m::(A ↛ B))

  (α * β) * γ == α * (β * γ) ⊣
    (A::Ob, B::Ob, C::Ob, D::Ob, W::Ob, X::Ob, Y::Ob, Z::Ob,
     m::(A↛B), n::(B↛C), p::(C↛D), u::(W↛X), v::(X↛Y), w::(Y↛Z),
     f::(A→W), g::(B→X), h::(C→Y), k::(D→Z),
     α::Cell(m,u,f,g), β::Cell(n,v,g,h), γ::Cell(p,w,h,k))
  α * pid(g) == α ⊣ (A::Ob, B::Ob, C::Ob, D::Ob, m::(A↛B), n::(C↛D),
                     f::(A→C), g::(B→D), α::Cell(m,n,f,g))
  pid(f) * α == α ⊣ (A::Ob, B::Ob, C::Ob, D::Ob, m::(A↛B), n::(C↛D),
                     f::(A→C), g::(B→D), α::Cell(m,n,f,g))

  # TODO: Interchange laws.
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

# Tabulators
############

""" Theory of a *double category with tabulators*

A tabulator of a proarrow is a double-categorical limit. It is a certain cell
with identity domain to the given proarrow that is universal among all cells of
that form. A double category "has tabulators" if the external identity functor
has a right adjoint. The values of this right adjoint are the apex objects of
its tabulators. The counit of the adjunction provides the universal cells.
Tabulators figure in the double-categorical limit construction theorem of
Grandis-Pare 1999. In the case where the double category is actually a
2-category, tabulators specialize to cotensors, a more familiar 2-categorical
limit.
"""
@theory ThDoubleCategoryWithTabulators{Ob,Hom,Pro,Cell,Tab} <: ThDoubleCategory{Ob,Hom,Pro,Cell} begin
  Tab(proarrow::(A ↛ B))::TYPE
  
  # data: a cell with domain p and two specified projections
  tabulator(p::(A↛B))::Tab(p) ⊣ (A::Ob,B::Ob)
  ob(τ::Tab(p))::Ob ⊣ (A::Ob,B::Ob,p::(A↛B))
  proj1(τ::Tab(p))::(ob(τ) → A) ⊣ (A::Ob, B::Ob, p::(A↛B))
  proj2(τ::Tab(p))::(ob(τ) → B) ⊣ (A::Ob, B::Ob, p::(A↛B))
  cell(τ::Tab(p))::Cell(pid(ob(τ)), p, proj1(τ), proj2(τ)) ⊣ 
    (A::Ob, B::Ob, p::(A↛B))
  
  # factorization existence
  universal(τ::Tab(p), θ::Cell(pid(X),p,f,g))::(X→ob(τ)) ⊣ 
    (A::Ob, B::Ob, X::Ob, p::(A↛B), f::(X→A), g::(X→B))
  universal(τ,θ) ⋅ proj1(τ) == f ⊣
    (A::Ob, B::Ob, X::Ob, p::(A↛B), f::(X→A), g::(X→B),
     τ::Tab(p), θ::Cell(pid(X),p,f,g))
  universal(τ,θ) ⋅ proj2(τ) == g ⊣
    (A::Ob, B::Ob, X::Ob, p::(A↛B), f::(X→A), g::(X→B),
     τ::Tab(p), θ::Cell(pid(X),p,f,g))
  pid(universal(τ,θ)) ⋅ cell(τ) == θ ⊣
    (A::Ob, B::Ob, X::Ob, p::(A↛B), f::(X→A), g::(X→B),
     τ::Tab(p), θ::Cell(pid(X),p,f,g))

  # uniqueness of factorization
  universal(τ, pid(h) ⋅ cell(τ)) == h ⊣ (A::Ob,B::Ob,X::Ob,p::(A↛B),
                                         τ::Tab(p),h::(X→ob(τ)))
end

# Equipment
###########

""" Theory of a *proarrow equipment*, or *equipment* for short

Equipments have also been called "framed bicategories," "fibrant double
categories," and "gregarious double categories" (?!).

References:

- Shulman, 2008: Framed bicategories and monoidal fibrations
- Cruttwell & Shulman, 2010: A unified framework for generalized multicategories
"""
@theory ThEquipment{Ob,Hom,Pro,Cell} <: ThDoubleCategory{Ob,Hom,Pro,Cell} begin
  companion(f::(A → B))::(A ↛ B) ⊣ (A::Ob, B::Ob)
  conjoint(f::(A → B))::(B ↛ A) ⊣ (A::Ob, B::Ob)

  # Binding cells (unit and counit) for companions and conjoints.
  companion_unit(f::(A → B))::Cell(pid(A), companion(f), id(A), f) ⊣ (A::Ob, B::Ob)
  companion_counit(f::(A → B))::Cell(companion(f), pid(B), f, id(B)) ⊣ (A::Ob, B::Ob)
  conjoint_unit(f::(A → B))::Cell(pid(A), conjoint(f), f, id(A)) ⊣ (A::Ob, B::Ob)
  conjoint_counit(f::(A → B))::Cell(conjoint(f), pid(B), id(B), f) ⊣ (A::Ob, B::Ob)

  # Triangle-style identities for binding cells.
  companion_unit(f) ⋅ companion_counit(f) == pid(f) ⊣ (A::Ob, B::Ob, f::(A → B))
  companion_unit(f) * companion_counit(f) == id(companion(f)) ⊣ (A::Ob, B::Ob, f::(A → B))
  conjoint_unit(f) ⋅ conjoint_counit(f) == pid(f) ⊣ (A::Ob, B::Ob, f::(A → B))
  conjoint_counit(f) * conjoint_unit(f) == id(conjoint(f)) ⊣ (A::Ob, B::Ob, f::(A → B))
end

# Monoidal double category
##########################

""" Theory of *monoidal double categories*

To avoid associators and unitors, we assume that the monoidal double category is
fully *strict*: both the double category and its monoidal product are strict.
Apart from assuming strictness, this theory agrees with the definition of a
monoidal double category in (Shulman 2010) and other recent works.

In a monoidal double category ``(D,⊗,I)``, the underlying categories ``D₀`` and
``D₁`` are each monoidal categories, ``(D₀,⊗₀,I₀)`` and ``(D₁,⊗₁,I₁)``, subject
to further axioms such as the source and target functors ``S, T: D₁ → D₀`` being
strict monoidal functors.

Despite the apparent asymmetry in this setup, the definition of a monoidal
double category unpacks to be nearly symmetric with respect to arrows and
proarrows, except that the monoidal unit ``I₀`` of ``D₀`` induces the monoidal
unit of ``D₁`` as ``I₁ = U(I₀)``.

References:

- Shulman, 2010: Constructing symmetric monoidal bicategories

FIXME: Should also inherit `ThMonoidalCategory{Ob,Hom}` but multiple inheritance
is not supported.
"""
@theory ThMonoidalDoubleCategory{Ob,Hom,Pro,Cell} <: ThDoubleCategory{Ob,Hom,Pro,Cell} begin
  @op (⊗) := otimes

  # Monoidal operations on D₀.
  otimes(A::Ob, B::Ob)::Ob
  otimes(f::(A → B), g::(C → D))::((A ⊗ C) → (B ⊗ D)) ⊣
    (A::Ob, B::Ob, C::Ob, D::Ob)
  munit()::Ob

  # Monoid axioms for (D₀,⊗₀,I₀).
  (A ⊗ B) ⊗ C == A ⊗ (B ⊗ C) ⊣ (A::Ob, B::Ob, C::Ob)
  A ⊗ munit() == A ⊣ (A::Ob)
  munit() ⊗ A == A ⊣ (A::Ob)
  (f ⊗ g) ⊗ h == f ⊗ (g ⊗ h) ⊣ (A::Ob, B::Ob, C::Ob, X::Ob, Y::Ob, Z::Ob,
                                f::(A → X), g::(B → Y), h::(C → Z))

  # Functorality axioms for (D₀,⊗₀,I₀).
  ((f ⊗ g) ⋅ (h ⊗ k) == (f ⋅ h) ⊗ (g ⋅ k)
    ⊣ (A::Ob, B::Ob, C::Ob, X::Ob, Y::Ob, Z::Ob,
       f::(A → B), h::(B → C), g::(X → Y), k::(Y → Z)))
  id(A ⊗ B) == id(A) ⊗ id(B) ⊣ (A::Ob, B::Ob)

  # Monoidal operations on D₁ + src/tgt are strict monoidal functors.
  otimes(m::(A ↛ B), n::(C ↛ D))::((A ⊗ C) ↛ (B ⊗ D)) ⊣
    (A::Ob, B::Ob, C::Ob, D::Ob)
  otimes(α::Cell(m,n,f,g), β::Cell(m′,n′,f′,g′))::Cell(m⊗m′,n⊗n′,f⊗f′,g⊗g′) ⊣
    (A::Ob, B::Ob, C::Ob, D::Ob, A′::Ob, B′::Ob, C′::Ob, D′::Ob,
     f::(A → C), g::(B → D), f′::(A′ → C′), g′::(B′ → D′),
     m::(A ↛ B), n::(C ↛ D), m′::(A′ ↛ B′), n′::(C′ ↛ D′))

  # Monoid axioms for (D₁,⊗₁,I₁).
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

  # Functorality axioms for (D₁,⊗₁,I₁).
  ((α ⊗ α′) ⋅ (β ⊗ β′)) == (α ⋅ β) ⊗ (α′ ⋅ β′) ⊣
    (A::Ob, B::Ob, C::Ob, A′::Ob, B′::Ob, C′::Ob,
     X::Ob, Y::Ob, Z::Ob, X′::Ob, Y′::Ob, Z′::Ob,
     f::(A→B), g::(X→Y), f′::(A′→B′), g′::(X′→Y′),
     h::(B→C), k::(Y→Z), h′::(B′→C′), k′::(Y′→Z′),
     m::(A↛X), n::(B↛Y), p::(C↛Z), m′::(A′↛X′), n′::(B′↛Y′), p′::(C′↛Z′),
     α::Cell(m,n,f,g), α′::Cell(m′,n′,f′,g′),
     β::Cell(n,p,h,k), β′::Cell(n′,p′,h′,k′))
  id(m ⊗ n) == id(m) ⊗ id(n) ⊣
    (A::Ob, B::Ob, X::Ob, Y::Ob, m::(A ↛ X), n::(B ↛ Y))

  # External functorality of ⊗: D×D → D and I: 1 → D.
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

  # Interchange of braiding with external composition.
  σ(m*n, m′*n′) == σ(m,m′) * σ(n,n′) ⊣
    (A::Ob, B::Ob, C::Ob, A′::Ob, B′::Ob, C′::Ob,
     m::(A↛B), n::(B↛C), m′::(A′↛B′), n′::(B′↛C′))
  σ(pid(A), pid(B)) == pid(σ(A,B)) ⊣ (A::Ob, B::Ob)
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

# Cartesian double category
###########################

""" Theory of a *cartesian double category*

Loosely speaking, a cartesian double category is a double category ``D`` such
that the underlying catgories ``D₀`` and ``D₁`` are both cartesian categories,
in a compatible way.

Reference: Aleiferi 2018, PhD thesis.
"""
@theory ThCartesianDoubleCategory{Ob,Hom,Pro,Cell} <: ThSymmetricMonoidalDoubleCategory{Ob,Hom,Pro,Cell} begin
  # Pairing and projection in D₀.
  pair(f::(A → B), g::(A → C))::(A → (B ⊗ C)) ⊣ (A::Ob, B::Ob, C::Ob)
  proj1(A::Ob, B::Ob)::((A ⊗ B) → A)
  proj2(A::Ob, B::Ob)::((A ⊗ B) → B)

  pair(f,g) ⋅ proj1(B,C) == f ⊣ (A::Ob, B::Ob, C::Ob, f::(A → B), g::(A → C))
  pair(f,g) ⋅ proj2(B,C) == g ⊣ (A::Ob, B::Ob, C::Ob, f::(A → B), g::(A → C))
  pair(h ⋅ proj1(B,C), h ⋅ proj2(B,C)) == h ⊣
    (A::Ob, B::Ob, C::Ob, h::(A → (B ⊗ C)))

  # Pairing and projection in D₁.
  pair(α::Cell(m,p,f,h), β::Cell(m,q,g,k))::Cell(m,p⊗q,pair(f,g),pair(h,k)) ⊣
    (A::Ob, B::Ob, W::Ob, X::Ob, Y::Ob, Z::Ob,
     f::(A → W), g::(A → Y), h::(B → X), k::(B → Z),
     m::(A ↛ B), p::(W ↛ X), q::(Y ↛ Z))
  proj1(m::(A ↛ B), n::(C ↛ D))::Cell(m⊗n, m, proj1(A,C), proj1(B,D)) ⊣
    (A::Ob, B::Ob, C::Ob, D::Ob)
  proj2(m::(A ↛ B), n::(C ↛ D))::Cell(m⊗n, n, proj2(A,C), proj2(B,D)) ⊣
    (A::Ob, B::Ob, C::Ob, D::Ob)

  # TODO: Pairing/projection axioms for D₁.

  # Interchange of pairing with external composition.
  pair(α * γ, β * δ) == pair(α,β) * pair(γ,δ) ⊣
    (A::Ob, B::Ob, C::Ob, P::Ob, Q::Ob, W::Ob, X::Ob, Y::Ob, Z::Ob,
     f::(A → W), g::(A → Y), h::(B → X), k::(B → Z), i::(C → P), j::(C → Q),
     m::(A ↛ B), n::(B ↛ C), p::(W ↛ X), q::(Y ↛ Z), u::(X ↛ P), v::(Z ↛ Q),
     α::Cell(m,p,f,h), β::Cell(m,q,g,k), γ::Cell(n,u,h,i), δ::Cell(n,v,k,j))
  pair(pid(f), pid(g)) == pid(pair(f,g)) ⊣
    (A::Ob, B::Ob, C::Ob, f::(A → B), g::(B → C))

  # Interchange of projection with external composition.
  proj1(m * n, p * q) == proj1(m, p) * proj2(n, q) ⊣
    (A::Ob, B::Ob, C::Ob, X::Ob, Y::Ob, Z::Ob,
     m::(A ↛ B), n::(B ↛ C), p::(X ↛ Y), q::(Y ↛ Z))
  proj2(m * n, p * q) == proj2(m, p) * proj2(n, q) ⊣
    (A::Ob, B::Ob, C::Ob, X::Ob, Y::Ob, Z::Ob,
     m::(A ↛ B), n::(B ↛ C), p::(X ↛ Y), q::(Y ↛ Z))
  proj1(pid(A), pid(B)) == pid(proj1(A, B)) ⊣ (A::Ob, B::Ob)
  proj2(pid(A), pid(B)) == pid(proj2(A, B)) ⊣ (A::Ob, B::Ob)
end
