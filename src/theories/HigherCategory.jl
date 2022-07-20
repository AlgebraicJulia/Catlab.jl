export ThCategory2, FreeCategory2, Hom2, Hom2Expr, composeV, composeH, *,
  ThDoubleCategory, FreeDoubleCategory, HomH, HomV, HomHExpr, HomVExpr,
  left, right, top, bottom, idH, idV, id2, id2V, id2H,
  ThMonoidalDoubleCategory, ThSymmetricMonoidalDoubleCategory,
  FreeSymmetricMonoidalDoubleCategory, braidH, braidV, σH, σV

import Base: *

abstract type Hom2Expr{T} <: CategoryExpr{T} end
abstract type HomVExpr{T} <: CategoryExpr{T} end
abstract type HomHExpr{T} <: CategoryExpr{T} end

# 2-category
############

""" Theory of (strict) *2-categories*
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

function show_unicode(io::IO, expr::Hom2Expr{:compose}; kw...)
  Syntax.show_unicode_infix(io, expr, "⋅"; kw...)
end
function show_unicode(io::IO, expr::Hom2Expr{:composeH}; kw...)
  Syntax.show_unicode_infix(io, expr, "*"; kw...)
end

function show_latex(io::IO, expr::Hom2Expr{:compose}; kw...)
  Syntax.show_latex_infix(io, expr, "\\cdot"; kw...)
end
function show_latex(io::IO, expr::Hom2Expr{:composeH}; kw...)
  Syntax.show_latex_infix(io, expr, "*"; kw...)
end

# Double category
#################

""" Theory of (strict) *double categories*
"""
@theory ThDoubleCategory{Ob,HomV,HomH,Hom2} begin
  Ob::TYPE
  """ Vertical morphism in a double category """
  HomV(dom::Ob, codom::Ob)::TYPE
  """ Horizontal morphism in a double category """
  HomH(dom::Ob, codom::Ob)::TYPE
  """ 2-cell in a double category """
  Hom2(top::HomH(A,B), bottom::HomH(C,D),
       left::HomV(A,C), right::HomV(B,D))::TYPE ⊣ (A::Ob, B::Ob, C::Ob, D::Ob)
  @op begin
    (→) := HomH
    (↓) := HomV
    (⇒) := Hom2
    (*) := composeH
    (⋅) := composeV
  end

  idH(A::Ob)::(A → A) ⊣ (A::Ob)
  idV(A::Ob)::(A ↓ A) ⊣ (A::Ob)
  composeH(f::(A → B), g::(B → C))::(A → C) ⊣ (A::Ob, B::Ob, C::Ob)
  composeV(f::(A ↓ B), g::(B ↓ C))::(A ↓ C) ⊣ (A::Ob, B::Ob, C::Ob)

  # Category axioms for horizontal morphisms
  ((f * g) * h == f * (g * h)
    ⊣ (A::Ob, B::Ob, C::Ob, D::Ob, f::(A → B), g::(B → C), h::(C → D)))
  f * idH(B) == f ⊣ (A::Ob, B::Ob, f::(A → B))
  idH(A) * f == f ⊣ (A::Ob, B::Ob, f::(A → B))

  # Category axioms for vertical morphisms
  ((f ⋅ g) ⋅ h == f ⋅ (g ⋅ h)
    ⊣ (A::Ob, B::Ob, C::Ob, D::Ob, f::(A ↓ B), g::(B ↓ C), h::(C ↓ D)))
  f ⋅ idV(B) == f ⊣ (A::Ob, B::Ob, f::(A ↓ B))
  idV(A) ⋅ f == f ⊣ (A::Ob, B::Ob, f::(A ↓ B))

  # Identity 2-cell on object
  id2(X::Ob)::Hom2(idH(X), idH(X), idV(X), idV(X)) ⊣ (X::Ob)
  # Identity 2-cell for vertical composition
  id2V(f::(X→Y))::Hom2(f, f, idV(X), idV(Y)) ⊣ (X::Ob, Y::Ob)
  # Identity 2-cell for horizontal composition
  id2H(f::(X↓Y))::Hom2(idH(X), idH(Y), f, f) ⊣ (X::Ob, Y::Ob)

  # Vertical composition of 2-cells
  composeV(α::Hom2(t,b,l,r), β::Hom2(b,b′,l′,r′))::Hom2(t, b′, l⋅l′, r⋅r′) ⊣
    (A::Ob, B::Ob, X::Ob, Y::Ob, C::Ob, D::Ob,
     t::(A→B), b::(X→Y), l::(A↓X), r::(B↓Y),
     b′::(C→D), l′::(X↓C), r′::(Y↓D))

  # Horizontal composition of 2-cells
  composeH(α::Hom2(t,b,l,r), β::Hom2(t′,b′,r,r′))::Hom2(t*t′, b*b′, l, r′) ⊣
    (A::Ob, B::Ob, X::Ob, Y::Ob, C::Ob, D::Ob,
     t::(A→X), b::(B→Y), l::(A↓B), r::(X↓Y),
     t′::(X→C), b′::(Y→D), r′::(C↓D))
end

# Convenience constructors
composeV(αs::AbstractVector) = foldl(composeV, αs)
composeV(α, β, γ, αs...) = composeV([α, β, γ, αs...])

""" Syntax for a double category.

Checks domains of morphisms but not 2-morphisms.
"""
@syntax FreeDoubleCategory{ObExpr,HomVExpr,HomHExpr,Hom2Expr} ThDoubleCategory begin
  composeV(f::HomV, g::HomV) = associate_unit(new(f,g; strict=true), idV)
  composeH(f::HomH, g::HomH) = associate_unit(new(f,g; strict=true), idH)
  composeV(α::Hom2, β::Hom2) = associate_unit(new(α,β), id2V)
  composeH(α::Hom2, β::Hom2) = associate_unit(new(α,β), id2H)
end

function show_unicode(io::IO, expr::Hom2Expr{:composeV}; kw...)
  Syntax.show_unicode_infix(io, expr, "⋅"; kw...)
end

function show_latex(io::IO, expr::Hom2Expr{:composeV}; kw...)
  Syntax.show_latex_infix(io, expr, "\\cdot"; kw...)
end

# Monoidal double category
##########################

""" Theory of *monoidal double categories*

To avoid associators and unitors, we assume the monoidal double category is
*strict* in both the horizontal and vertical directions. Apart from assuming
strictness, this theory follows the definition of a monoidal double category in
(Shulman, 2010, Constructing symmetric monoidal bicategories) and other recent
papers, starting from an internal category ``(S,T: D₁ ⇉ D₀, U: D₀ → D₁,
*: D₁ ×_{D₀} D₁ → D₁)`` in **Cat** where

- the objects of ``D₀`` are objects
- the morphisms of ``D₀`` are vertical 1-cells
- the objects of ``D₁`` are horizontal 1-cells
- the morphisms of ``D₁`` are 2-cells.

The top and bottom of a 2-cell are given by domain and codomain in ``D₁`` and
the left and right are given by the functors ``S,T``. In a monoidal double
category, ``D₀`` and ``D₁`` are each required to be monoidal categories, subject
to further axioms such as ``S`` and ``T`` being strict monoidal functors.

Despite the apparent asymmetry in this setup, the definition of a monoidal
double category unpacks to be nearly symmetric with respect to horizontal and
vertical, except that the monoidal unit ``I`` of ``D₀`` induces the monoidal
unit of ``D₁`` as ``U(I)``, which I think has no analogue in the vertical
direction.
"""
@theory ThMonoidalDoubleCategory{Ob,HomV,HomH,Hom2} <: ThDoubleCategory{Ob,HomV,HomH,Hom2} begin
  otimes(A::Ob, B::Ob)::Ob
  otimes(f::(A → B), g::(C → D))::((A ⊗ C) → (B ⊗ D)) ⊣
    (A::Ob, B::Ob, C::Ob, D::Ob)
  otimes(f::(A ↓ B), g::(C ↓ D))::((A ⊗ C) ↓ (B ⊗ D)) ⊣
    (A::Ob, B::Ob, C::Ob, D::Ob)
  otimes(f::Hom2(t,b,l,r),g::Hom2(t′,b′,l′,r′))::Hom2(t⊗t′,b⊗b′,l⊗l′,r⊗r′) ⊣
    (A::Ob, B::Ob, C::Ob, D::Ob, E::Ob, F::Ob, G::Ob, H::Ob,
     t::(A → B), b::(C → D), l::(A ↓ C), r::(B ↓ D),
     t′::(E → F), b′::(G → H), l′::(E ↓ G), r′::(F ↓ H))

  @op (⊗) := otimes
  munit()::Ob

  # Monoid axioms, vertical.
  (A ⊗ B) ⊗ C == A ⊗ (B ⊗ C) ⊣ (A::Ob, B::Ob, C::Ob)
  A ⊗ munit() == A ⊣ (A::Ob)
  munit() ⊗ A == A ⊣ (A::Ob)
  (f ⊗ g) ⊗ h == f ⊗ (g ⊗ h) ⊣ (A::Ob, B::Ob, C::Ob, X::Ob, Y::Ob, Z::Ob,
                                f::(A ↓ X), g::(B ↓ Y), h::(C ↓ Z))

  # Monoid axioms, horizontal.
  (f ⊗ g) ⊗ h == f ⊗ (g ⊗ h) ⊣ (A::Ob, B::Ob, C::Ob, X::Ob, Y::Ob, Z::Ob,
                                f::(A → X), g::(B → Y), h::(C → Z))
  f ⊗ idH(munit()) == f ⊣ (A::Ob, B::Ob, f::(A → B))
  idH(munit()) ⊗ f == f ⊣ (A::Ob, B::Ob, f::(A → B))
  (α ⊗ β) ⊗ γ == α ⊗ (β ⊗ γ) ⊣
    (A::Ob, B::Ob, C::Ob, D::Ob, E::Ob, F::Ob,
     G::Ob, H::Ob, I::Ob, J::Ob, K::Ob, L::Ob,
     t1::(A → B), b1::(C → D), l1::(A ↓ C), r1::(B ↓ D),
     t2::(E → F), b2::(G → H), l2::(E ↓ G), r2::(F ↓ H),
     t3::(I → J), b3::(K → L), l3::(I ↓ K), r3::(J ↓ L),
     α::Hom2(t1, b1, l1, r1), β::Hom2(t2, b2, l2, r2), γ::Hom2(t3, b3, l3, r3))

  # Functorality axioms.
  ((f ⊗ g) * (h ⊗ k) == (f * h) ⊗ (g * k)
    ⊣ (A::Ob, B::Ob, C::Ob, X::Ob, Y::Ob, Z::Ob,
       f::(A → B), h::(B → C), g::(X → Y), k::(Y → Z)))
  ((f ⊗ g) ⋅ (h ⊗ k) == (f ⋅ h) ⊗ (g ⋅ k)
    ⊣ (A::Ob, B::Ob, C::Ob, X::Ob, Y::Ob, Z::Ob,
       f::(A ↓ B), h::(B ↓ C), g::(X ↓ Y), k::(Y ↓ Z)))
  ((α ⊗ β) ⋅ (γ ⊗ δ) == (α ⋅ γ) ⊗ (β ⋅ δ)
    ⊣ (A::Ob, B::Ob, C::Ob, D::Ob, E::Ob, F::Ob, G::Ob, H::Ob,
       I::Ob, J::Ob, K::Ob, L::Ob, M::Ob, N::Ob, O::Ob, P::Ob,
       t1::(A → B), b1::(C → D), l1::(A ↓ C), r1::(B ↓ D),
       t2::(E → F), b2::(G → H), l2::(E ↓ G), r2::(F ↓ H),
       t3::(I → J), b3::(K → L), l3::(I ↓ K), r3::(J ↓ L),
       t4::(M → N), b4::(O → P), l4::(M ↓ O), r4::(N ↓ P),
       α::Hom2(t1, b1, l1, r1), β::Hom2(t2, b2, l2, r2),
       γ::Hom2(t3, b3, l3, r3), δ::Hom2(t4, b4, l4, r4)))
  idH(A ⊗ B) == idH(A) ⊗ idH(B) ⊣ (A::Ob, B::Ob)
  idV(A ⊗ B) == idV(A) ⊗ idV(B) ⊣ (A::Ob, B::Ob)
  id2(A ⊗ B) == id2(A) ⊗ id2(B) ⊣ (A::Ob, B::Ob)
  id2H(f ⊗ g) == id2H(f) ⊗ id2H(g) ⊣ (A::Ob, B::Ob, C::Ob, D::Ob,
                                      f::(A↓C), g::(B↓D))
  id2V(f ⊗ g) == id2V(f) ⊗ id2V(g) ⊣ (A::Ob, B::Ob, C::Ob, D::Ob,
                                      f::(A→C), g::(B→D))
end

""" Theory of (strict) *symmetric monoidal double categories*

Unlike classical double categories, symmetric monoidal double categories do not
treat the vertical and horizontal directions on an equal footing, even in the
strict case. See [`MonoidalDoubleCategory`](@ref) for details and references.
"""
@theory ThSymmetricMonoidalDoubleCategory{Ob,HomV,HomH,Hom2} <: ThMonoidalDoubleCategory{Ob,HomV,HomH,Hom2} begin
  braidV(A::Ob, B::Ob)::((A ⊗ B) ↓ (B ⊗ A))
  braidH(f::(A → C), g::(B → D))::Hom2((f ⊗ g), (g ⊗ f), σV(A,B), σV(C,D)) ⊣
    (A::Ob, B::Ob, C::Ob, D::Ob)
  @op (σV) := braidV
  @op (σH) := braidH

  # Involutivity axioms.
  σV(A,B) ⋅ σV(B,A) == idV(A ⊗ B) ⊣ (A::Ob, B::Ob)
  σH(f,g) ⋅ σH(g,f) == id2V(f ⊗ g) ⊣ (A::Ob, B::Ob, C::Ob, D::Ob,
                                      f::(A → C), g::(B → D))

  # Naturality axioms.
  (f⊗g) ⋅ σV(C,D) == σV(A,B) ⋅ (g⊗f) ⊣ (A::Ob, B::Ob, C::Ob, D::Ob,
                                        f::(A ↓ C), g::(B ↓ D))
  ((α⊗β) ⋅ σH(h,k) == σH(f,g) ⋅ (β⊗α) ⊣
    (A::Ob, B::Ob, C::Ob, D::Ob, E::Ob, F::Ob, G::Ob, H::Ob,
     f::(A → C), g::(B → D), h::(E → G), k::(F → H),
     ℓ1::(A ↓ E), r1::(C ↓ G), ℓ2::(B ↓ F), r2::(D ↓ H),
     α::Hom2(f,h,ℓ1,r1), β::Hom2(g,k,ℓ2,r2)))

  # Coherence axioms.
  σV(A,B⊗C) == (σV(A,B) ⊗ idV(C)) ⋅ (idV(B) ⊗ σV(A,C)) ⊣ (A::Ob, B::Ob, C::Ob)
  σV(A⊗B,C) == (idV(A) ⊗ σV(B,C)) ⋅ (σV(A,C) ⊗ idV(B)) ⊣ (A::Ob, B::Ob, C::Ob)
  (σH(f,g⊗h) == (σH(f,g) ⊗ id2V(h)) ⋅ (id2V(g) ⊗ σH(f,h)) ⊣
    (A::Ob, B::Ob, C::Ob, D::Ob, E::Ob, F::Ob,
     f::(A → D), g::(B → E), h::(C → F)))
  (σH(f⊗g,h) == (id2V(f) ⊗ σH(g,h)) ⋅ (σH(f,h) ⊗ id2V(g)) ⊣
    (A::Ob, B::Ob, C::Ob, D::Ob, E::Ob, F::Ob,
     f::(A → D), g::(B → E), h::(C → F)))
end

@syntax FreeSymmetricMonoidalDoubleCategory{ObExpr,HomVExpr,HomHExpr,Hom2Expr} ThSymmetricMonoidalDoubleCategory begin
  otimes(A::Ob, B::Ob) = associate_unit(new(A,B), munit)
  otimes(f::HomV, g::HomV) = associate(new(f,g))
  otimes(f::HomH, g::HomH) = associate(new(f,g))
  otimes(f::Hom2, g::Hom2) = associate(new(f,g))
  composeV(f::HomV, g::HomV) = associate_unit(new(f,g; strict=true), idV)
  composeH(f::HomH, g::HomH) = associate_unit(new(f,g; strict=true), idH)
  composeV(α::Hom2, β::Hom2) = associate_unit(new(α,β), id2V)
  composeH(α::Hom2, β::Hom2) = associate_unit(new(α,β), id2H)
end

function show_unicode(io::IO, expr::HomVExpr{:braidV}; kw...)
  Syntax.show_unicode_infix(io, expr, "σV"; kw...)
end
function show_unicode(io::IO, expr::Hom2Expr{:braidH}; kw...)
  Syntax.show_unicode_infix(io, expr, "σH"; kw...)
end

function show_latex(io::IO, expr::HomVExpr{:braidV}; kw...)
  Syntax.show_latex_script(io, expr, "\\sigmaV")
end
function show_latex(io::IO, expr::Hom2Expr{:braidH}; kw...)
  Syntax.show_latex_script(io, expr, "\\sigmaH")
end
