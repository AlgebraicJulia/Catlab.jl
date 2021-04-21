export Category, FreeCategory, Ob, Hom, dom, codom, id, compose, ⋅,
  Copresheaf, Presheaf, El, ob, act, coact

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

# (Co)presheaf
##############

""" Theory of *copresheaves*.

Axiomatized as a covariant category action.
"""
@theory Copresheaf{Ob,Hom,El} <: Category{Ob,Hom} begin
  # copresheaf = object-indexed family
  El(ob::Ob)::TYPE

  # functoriality = covariant action
  act(x::El(A), f::Hom(A,B))::El(B) ⊣ (A::Ob, B::Ob)

  # action equations
  act(act(x, f), g) == act(x, (f ⋅ g)) ⊣
    (A::Ob, B::Ob, C::Ob, f::(A → B), g::(B → C), x::El(A))
  act(x, id(A)) == x ⊣ (A::Ob, x::El(A))
end

""" Theory of *presheaves*.

Axiomatized as a contravariant category action.
"""
@theory Presheaf{Ob,Hom,El} <: Category{Ob,Hom} begin
  # presheaf = object-indexed family
  El(ob::Ob)::TYPE

  # functoriality = contravariant action
  coact(f::Hom(A,B), x::El(B))::El(A) ⊣ (A::Ob, B::Ob)

  # action equations
  coact(f, coact(g, x)) == coact((f ⋅ g), x) ⊣
    (A::Ob, B::Ob, C::Ob, f::(A → B), g::(B → C), x::El(C))
  coact(id(A), x) == x ⊣ (A::Ob, x::El(A))
end