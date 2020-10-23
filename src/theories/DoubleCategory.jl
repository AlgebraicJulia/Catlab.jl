export DoubleCategory, FreeDoubleCategory, HomH, HomV, Hom2, idH, idV,
  id2, id2V, id2H, composeH, composeV, ⋆, MonoidalDoubleCategory,
  SymmetricMonoidalDoubleCategory, FreeSymmetricMonoidalDoubleCategory,
  braidH, braidV, σH, σV

# Double category
#################

""" Theory of (strict) *double categories*
"""
@theory DoubleCategory{Ob,HomV,HomH,Hom2} begin
  # """ Object in a category """
  Ob::TYPE
  """ Vertical Morphism in a double category """
  HomV(dom::Ob, codom::Ob)::TYPE
  """ Horizontal Morphism in a double category """
  HomH(dom::Ob, codom::Ob)::TYPE
  """ 2-cell in a double category """
  Hom2(top::HomH(A,B),
       bottom::HomH(C,D),
       left::HomV(A,C),
       right::HomV(B,D))::TYPE ⊣ (A::Ob, B::Ob, C::Ob, D::Ob)
  @op begin
    (→) := HomH
    (↓) := HomV
    (⇒) := Hom2
    (⋆) := composeH
    (⋅) := composeV
  end

  idH(A::Ob)::(A → A) ⊣ (A::Ob)
  idV(A::Ob)::(A ↓ A) ⊣ (A::Ob)
  composeH(f::(A → B), g::(B → C))::(A → C) ⊣ (A::Ob, B::Ob, C::Ob)
  composeV(f::(A ↓ B), g::(B ↓ C))::(A ↓ C) ⊣ (A::Ob, B::Ob, C::Ob)

  # Category axioms for Horizontal morphisms
  ((f ⋆ g) ⋆ h == f ⋆ (g ⋆ h)
    ⊣ (A::Ob, B::Ob, C::Ob, D::Ob, f::(A → B), g::(B → C), h::(C → D)))
  f ⋆ idH(B) == f ⊣ (A::Ob, B::Ob, f::(A → B))
  idH(A) ⋆ f == f ⊣ (A::Ob, B::Ob, f::(A → B))

  # Category axioms for Vertical morphisms
  ((f ⋅ g) ⋅ h == f ⋅ (g ⋅ h)
    ⊣ (A::Ob, B::Ob, C::Ob, D::Ob, f::(A ↓ B), g::(B ↓ C), h::(C ↓ D)))
  f ⋅ idV(B) == f ⊣ (A::Ob, B::Ob, f::(A ↓ B))
  idV(A) ⋅ f == f ⊣ (A::Ob, B::Ob, f::(A ↓ B))

  # identity two cell on 1 object
  id2(X::Ob)::Hom2(idH(X), idH(X), idV(X), idV(X)) ⊣ (X::Ob)
  # identity two cell for vertical composition
  id2V(f::(X→Y))::Hom2(f, f, idV(X), idV(Y)) ⊣ (X::Ob, Y::Ob)
  # identity two cell for horizontal composition
  id2H(f::(X↓Y))::Hom2(idH(X), idH(Y), f, f) ⊣ (X::Ob, Y::Ob)

  # Vertical composition of 2-cells
  composeV(
    α::Hom2(t,b,l,r),
    β::Hom2(b,b2,l2,r2)
  )::Hom2(t, b2, l⋅l2, r⋅r2)  ⊣ (A::Ob, B::Ob, X::Ob, Y::Ob, C::Ob, D::Ob,
                                 t::(A→B), b::(X→Y), l::(A↓X), r::(B↓Y),
                                 b2::(C→D), l2::(X↓C), r2::(Y↓D))

  # Horizontal composition of 2-cells
  composeH(
    α::Hom2(t,b,l,r),
    β::Hom2(t2,b2,r,r2)
  )::Hom2(t⋆t2, b⋆b2, l, r2)  ⊣ (A::Ob, B::Ob, X::Ob, Y::Ob, C::Ob, D::Ob,
                                 t::(A→X), b::(B→Y), l::(A↓B), r::(X↓Y),
                                 t2::(X→C), b2::(Y→D), r2::(C↓D))
end

# Convenience constructors
composeH(αs::Vector) = foldl(composeH, αs)
composeV(αs::Vector) = foldl(composeV, αs)
composeH(α, β, γ, αs...) = composeH([α, β, γ, αs...])
composeV(α, β, γ, αs...) = composeV([α, β, γ, αs...])


""" Syntax for a double category.

Checks domains of morphisms but not 2-morphisms.
"""
@syntax FreeDoubleCategory{ObExpr,HomVExpr, HomHExpr,Hom2Expr} DoubleCategory begin
  compose(f::HomV, g::HomV) = associate(new(f,g; strict=true))
  compose(f::HomH, g::HomH) = associate(new(f,g; strict=true))
  composeH(α::Hom2, β::Hom2) = associate(new(α,β))
  composeV(α::Hom2, β::Hom2) = associate(new(α,β))
end

function show_unicode(io::IO, expr::Hom2Expr{:composeV}; kw...)
  Syntax.show_unicode_infix(io, expr, "⋅"; kw...)
end
function show_unicode(io::IO, expr::Hom2Expr{:composeH}; kw...)
  Syntax.show_unicode_infix(io, expr, "*"; kw...)
end

function show_latex(io::IO, expr::Hom2Expr{:composeV}; kw...)
  Syntax.show_latex_infix(io, expr, "\\cdot"; kw...)
end
function show_latex(io::IO, expr::Hom2Expr{:composeH}; kw...)
  Syntax.show_latex_infix(io, expr, "\\star"; kw...)
end

# Monoidal category
###################

""" Theory of *monoidal double categories*

To avoid associators and unitors, we assume the monoidal double category is
*strict*. By the coherence theorem there is no loss of generality, but we may
add a theory for weak monoidal categories later.
"""
@theory MonoidalDoubleCategory{Ob,HomV,HomH,Hom2} <: DoubleCategory{Ob,HomV,HomH,Hom2} begin
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

  # Monoid axioms.
  (A ⊗ B) ⊗ C == A ⊗ (B ⊗ C) ⊣ (A::Ob, B::Ob, C::Ob)
  A ⊗ munit() == A ⊣ (A::Ob)
  munit() ⊗ A == A ⊣ (A::Ob)
  (f ⊗ g) ⊗ h == f ⊗ (g ⊗ h) ⊣ (A::Ob, B::Ob, C::Ob, X::Ob, Y::Ob, Z::Ob,
                                 f::(A → X), g::(B → Y), h::(C → Z))
  (f ⊗ g) ⊗ h == f ⊗ (g ⊗ h) ⊣ (A::Ob, B::Ob, C::Ob, X::Ob, Y::Ob, Z::Ob,
                                 f::(A ↓ X), g::(B ↓ Y), h::(C ↓ Z))
  (α ⊗ β) ⊗ γ == α ⊗ (β ⊗ γ) ⊣ (A::Ob, B::Ob, C::Ob, D::Ob,
                                E::Ob, F::Ob, G::Ob, H::Ob,
                                I::Ob, J::Ob, K::Ob, L::Ob,
                                t1::(A → B), b1::(C → D), l1::(A ↓ C), r1::(B ↓ D),
                                t2::(E → F), b2::(G → H), l2::(E ↓ G), r2::(F ↓ H),
                                t3::(I → J), b3::(K → L), l3::(I ↓ K), r3::(J ↓ L),
                                α::Hom2(t1, b1, l1, r1),
                                β::Hom2(t2, b2, l2, r2),
                                γ::Hom2(t3, b3, l3, r3))

  # Functorality axioms.
  ((f ⊗ g) ⋅ (h ⊗ k) == (f ⋅ h) ⊗ (g ⋅ k)
    ⊣ (A::Ob, B::Ob, C::Ob, X::Ob, Y::Ob, Z::Ob,
       f::(A → B), h::(B → C), g::(X → Y), k::(Y → Z)))
  ((f ⊗ g) ⋅ (h ⊗ k) == (f ⋅ h) ⊗ (g ⋅ k)
    ⊣ (A::Ob, B::Ob, C::Ob, X::Ob, Y::Ob, Z::Ob,
       f::(A ↓ B), h::(B ↓ C), g::(X ↓ Y), k::(Y ↓ Z)))
  ((α ⊗ β) ⋅ (γ ⊗ δ) == (α ⋅ γ) ⊗ (β ⋅ δ)
    ⊣ (A::Ob, B::Ob, C::Ob, D::Ob,
       E::Ob, F::Ob, G::Ob, H::Ob,
       I::Ob, J::Ob, K::Ob, L::Ob,
       M::Ob, N::Ob, O::Ob, P::Ob,
       t1::(A → B), b1::(C → D), l1::(A ↓ C), r1::(B ↓ D),
       t2::(E → F), b2::(G → H), l2::(E ↓ G), r2::(F ↓ H),
       t3::(I → J), b3::(K → L), l3::(I ↓ K), r3::(J ↓ L),
       t4::(M → N), b4::(O → P), l4::(M ↓ O), r4::(N ↓ P),
       α::Hom2(t1, b1, l1, r1),
       β::Hom2(t2, b2, l2, r2),
       γ::Hom2(t3, b3, l3, r3),
       δ::Hom2(t4, b4, l4, r4)))
  idH(A ⊗ B) == idH(A) ⊗ idH(B) ⊣ (A::Ob, B::Ob)
  idV(A ⊗ B) == idV(A) ⊗ idV(B) ⊣ (A::Ob, B::Ob)
  id2(A ⊗ B) == id2(A) ⊗ id2(B) ⊣ (A::Ob, B::Ob)
  id2H(l) == id2H(r1) ⊗ id2H(r2) ⊣ (A::Ob, B::Ob, C::Ob, D::Ob,
                                    l::((A⊗B)↓(C⊗D)), r1::(A↓C), r2::(B↓D))
  id2V(l) == id2V(r1) ⊗ id2V(r2) ⊣ (A::Ob, B::Ob, C::Ob, D::Ob,
                                    l::((A⊗B)→(C⊗D)), r1::(A→C), r2::(B→D))
end

""" Theory of (strict) *symmetric monoidal double categories*
"""
@theory SymmetricMonoidalDoubleCategory{Ob,HomV,HomH,Hom2} <: MonoidalDoubleCategory{Ob,HomV,HomH,Hom2} begin
  braidH(A::Ob, B::Ob)::((A ⊗ B) → (B ⊗ A))
  braidV(A::Ob, B::Ob)::((A ⊗ B) ↓ (B ⊗ A))
  @op (σH) := braidH
  @op (σV) := braidV

  # Involutivity axiom.
  σH(A,B) ⋅ σH(B,A) == idH(A ⊗ B) ⊣ (A::Ob, B::Ob)
  σV(A,B) ⋅ σV(B,A) == idV(A ⊗ B) ⊣ (A::Ob, B::Ob)

  # Coherence axioms.
  σH(A,B⊗C) == (σH(A,B) ⊗ idH(C)) ⋅ (idH(B) ⊗ σH(A,C)) ⊣ (A::Ob, B::Ob, C::Ob)
  σV(A⊗B,C) == (idV(A) ⊗ σV(B,C)) ⋅ (σV(A,C) ⊗ idV(B)) ⊣ (A::Ob, B::Ob, C::Ob)

  # Naturality axiom.
  (f ⊗ g) ⋅ σH(B,D) == σH(A,C) ⋅ (g ⊗ f) ⊣ (A::Ob, B::Ob, C::Ob, D::Ob,
                                           f::(A → B), g::(C → D))
  (f ⊗ g) ⋅ σV(B,D) == σV(A,C) ⋅ (g ⊗ f) ⊣ (A::Ob, B::Ob, C::Ob, D::Ob,
                                           f::(A ↓ B), g::(C ↓ D))
end

@syntax FreeSymmetricMonoidalDoubleCategory{ObExpr,HomVExpr,HomHExpr,Hom2Expr} SymmetricMonoidalDoubleCategory begin
  otimes(A::Ob, B::Ob) = associate_unit(new(A,B), munit)
  otimes(f::HomV, g::HomV) = associate(new(f,g))
  otimes(f::HomH, g::HomH) = associate(new(f,g))
  otimes(f::Hom2, g::Hom2) = associate(new(f,g))
  compose(f::HomV, g::HomV) = associate(new(f,g; strict=true))
  compose(f::HomH, g::HomH) = associate(new(f,g; strict=true))
  composeH(α::Hom2, β::Hom2) = associate(new(α,β))
  composeV(α::Hom2, β::Hom2) = associate(new(α,β))
end

function show_unicode(io::IO, expr::HomHExpr{:braidH}; kw...)
  Syntax.show_unicode_infix(io, expr, "σH"; kw...)
end
function show_unicode(io::IO, expr::HomVExpr{:braidV}; kw...)
  Syntax.show_unicode_infix(io, expr, "σV"; kw...)
end

function show_latex(io::IO, expr::HomHExpr{:braidH}; kw...)
  Syntax.show_latex_script(io, expr, "\\sigmaH")
end

function show_latex(io::IO, expr::HomVExpr{:braidV}; kw...)
  Syntax.show_latex_script(io, expr, "\\sigmaV")
end
