export Category, FreeCategory, Ob, Hom, dom, codom, id, compose, ⋅,
  Category2, FreeCategory2, Hom2, compose2, 
  DoubleCategory, HomH, HomV, composeH, composeV, FreeDoubleCategory

import Base: show

# Category
##########

""" Theory of *categories* (with no extra structure)

**Warning**: We compose functions from left to right, i.e., if f:A→B and g:B→C
then compose(f,g):A→C. Under this convention function are applied on the right,
e.g., if a∈A then af∈B.

We retain the usual meaning of the symbol ∘ (\\circ), i.e., g∘f = compose(f,g).
This usage is too entrenched to overturn, inconvenient though it may be.
We use symbol ⋅ (\\cdot) for diagrammatic composition: f⋅g = compose(f,g).
"""
@theory Category{Ob,Hom} begin
  # Unicode aliases.
  @op begin
    (→) := Hom
    (⋅) := compose
  end

  """ Object in a category """
  Ob::TYPE

  """ Morphism in a category """
  Hom(dom::Ob,codom::Ob)::TYPE

  id(A::Ob)::(A → A)
  compose(f::(A → B), g::(B → C))::(A → C) ⊣ (A::Ob, B::Ob, C::Ob)

  # Category axioms.
  ((f ⋅ g) ⋅ h == f ⋅ (g ⋅ h)
    ⊣ (A::Ob, B::Ob, C::Ob, D::Ob, f::(A → B), g::(B → C), h::(C → D)))
  f ⋅ id(B) == f ⊣ (A::Ob, B::Ob, f::(A → B))
  id(A) ⋅ f == f ⊣ (A::Ob, B::Ob, f::(A → B))
end

# Convenience constructors
compose(fs::Vector) = foldl(compose, fs)
compose(f, g, h, fs...) = compose([f, g, h, fs...])

@syntax FreeCategory{ObExpr,HomExpr} Category begin
  compose(f::Hom, g::Hom) = associate(new(f,g; strict=true))
end

function show_unicode(io::IO, expr::HomExpr{:compose}; kw...)
  Syntax.show_unicode_infix(io, expr, "⋅"; kw...)
end

function show_latex(io::IO, expr::HomExpr{:id}; kw...)
  Syntax.show_latex_script(io, expr, "\\mathrm{id}")
end
function show_latex(io::IO, expr::HomExpr{:compose}; paren::Bool=false, kw...)
  Syntax.show_latex_infix(io, expr, "\\cdot"; paren=paren)
end

function show(io::IO, ::MIME"text/latex", expr::GATExpr)
  print(io, "\$")
  show_latex(io, expr)
  print(io, "\$")
end

function show(io::IO, ::MIME"text/latex", expr::HomExpr)
  print(io, "\$")
  show_latex(io, expr)
  print(io, " : ")
  show_latex(io, dom(expr))
  print(io, " \\to ")
  show_latex(io, codom(expr))
  print(io, "\$")
end

# 2-category
############

""" Theory of (strict) *2-categories*
"""
@signature Category2{Ob,Hom,Hom2} <: Category{Ob,Hom} begin
  """ 2-morphism in a 2-category """
  Hom2(dom::Hom(A,B), codom::Hom(A,B))::TYPE ⊣ (A::Ob, B::Ob)
  @op (⇒) := Hom2

  # Hom categories: Vertical composition
  id(f)::(f ⇒ f) ⊣ (A::Ob, B::Ob, f::(A ⇒ B))
  compose(α::(f ⇒ g), β::(g ⇒ h))::(f ⇒ h) ⊣
    (A::Ob, B::Ob, f::(A → B), g::(A → B), h::(A → B))

  # Horizontal compostion
  compose2(α::(f ⇒ g), β::(h ⇒ k))::((f ⋅ h) ⇒ (g ⋅ k)) ⊣
    (A::Ob, B::Ob, C::Ob, f::(A → B), g::(A → B), h::(B → C), k::(B → C))
end

# Convenience constructors
compose2(αs::Vector) = foldl(compose2, αs)
compose2(α, β, γ, αs...) = compose2([α, β, γ, αs...])

""" Syntax for a 2-category.

Checks domains of morphisms but not 2-morphisms.
"""
@syntax FreeCategory2{ObExpr,HomExpr,Hom2Expr} Category2 begin
  compose(f::Hom, g::Hom) = associate(new(f,g; strict=true))
  compose(α::Hom2, β::Hom2) = associate(new(α,β))
  compose2(α::Hom2, β::Hom2) = associate(new(α,β))
end

function show_unicode(io::IO, expr::Hom2Expr{:compose}; kw...)
  Syntax.show_unicode_infix(io, expr, "⋅"; kw...)
end
function show_unicode(io::IO, expr::Hom2Expr{:compose2}; kw...)
  Syntax.show_unicode_infix(io, expr, "*"; kw...)
end

function show_latex(io::IO, expr::Hom2Expr{:compose}; kw...)
  Syntax.show_latex_infix(io, expr, "\\cdot"; kw...)
end
function show_latex(io::IO, expr::Hom2Expr{:compose2}; kw...)
  Syntax.show_latex_infix(io, expr, "*"; kw...)
end


###########
# Double Category
###########

""" Theory of (strict) *double categories*
"""
@theory DoubleCategory{Ob,HomV,HomH,Hom2} begin
  # """ Object in a category """
  Ob::TYPE
  """ Horizontal Morphism in a double category """
  HomH(dom::Ob, codom::Ob)::TYPE
  """ Vertical Morphism in a double category """
  HomV(dom::Ob, codom::Ob)::TYPE
  """ 2-cell in a double category """
  Hom2(top::HomH(A,B),
       bottom::HomH(C,D),
       left::HomV(A,C),
       right::HomV(B,D))::TYPE ⊣ (A::Ob, B::Ob, C::Ob, D::Ob)
  @op begin
    (→) := HomH
    (↓) := HomV
    (⇒) := Hom2
    (⋅) := composeH
    (⋆) := composeV
  end

  idH(A::Ob)::(A → A) ⊣ (A::Ob)
  idV(A::Ob)::(A ↓ A) ⊣ (A::Ob)
  composeH(f::(A → B), g::(B → C))::(A → C) ⊣ (A::Ob, B::Ob, C::Ob)
  composeV(f::(A ↓ B), g::(B ↓ C))::(A ↓ C) ⊣ (A::Ob, B::Ob, C::Ob)

  # Category axioms for Horizontal morphisms
  ((f ⋅ g) ⋅ h == f ⋅ (g ⋅ h)
    ⊣ (A::Ob, B::Ob, C::Ob, D::Ob, f::(A → B), g::(B → C), h::(C → D)))
  f ⋅ idH(B) == f ⊣ (A::Ob, B::Ob, f::(A → B))
  idH(A) ⋅ f == f ⊣ (A::Ob, B::Ob, f::(A → B))

  # Category axioms for Vertical morphisms
  ((f ⋅ g) ⋅ h == f ⋅ (g ⋅ h)
    ⊣ (A::Ob, B::Ob, C::Ob, D::Ob, f::(A ↓ B), g::(B ↓ C), h::(C ↓ D)))
  f ⋅ idV(B) == f ⊣ (A::Ob, B::Ob, f::(A ↓ B))
  idV(A) ⋅ f == f ⊣ (A::Ob, B::Ob, f::(A ↓ B))

  # identity two cell on 1 object
  id2(X::Ob)::Hom2(X→X, X→X, X↓X, X↓X)          ⊣ (X::Ob)
  id2(X) == id2(idH(X), idH(X), idV(X), idV(X)) ⊣ (X::Ob)
  # identity two cell from a HomH
  id2(f::(X→Y))::Hom2(X→Y, X→Y, X↓X, Y↓Y) ⊣ (X::Ob, Y::Ob)
  id2(f) == Hom2(f, f, idV(X), idV(Y))    ⊣ (X::Ob, Y::Ob, f::(X→Y))
  # identity two cell from a HomV
  id2(f::(X↓Y))::Hom2(X→X, Y→Y, X↓Y, X↓Y) ⊣ (X::Ob, Y::Ob)
  id2(f) == Hom2(idH(X), idH(Y), f, f)    ⊣ (X::Ob, Y::Ob, f::(X→Y))

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
  )::Hom2(t⋅t2, b⋅b2, l, r2)  ⊣ (A::Ob, B::Ob, X::Ob, Y::Ob, C::Ob, D::Ob,
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

function show_unicode(io::IO, expr::Hom2Expr{:composeH}; kw...)
  Syntax.show_unicode_infix(io, expr, "⋅"; kw...)
end
function show_unicode(io::IO, expr::Hom2Expr{:composeV}; kw...)
  Syntax.show_unicode_infix(io, expr, "*"; kw...)
end

function show_latex(io::IO, expr::Hom2Expr{:composeH}; kw...)
  Syntax.show_latex_infix(io, expr, "\\cdot"; kw...)
end
function show_latex(io::IO, expr::Hom2Expr{:composeV}; kw...)
  Syntax.show_latex_infix(io, expr, "\\star"; kw...)
end