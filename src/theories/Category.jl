export Category, FreeCategory, Ob, Hom, dom, codom, id, compose, ⋅,
  Copresheaf, FreeCopresheaf, El, ElExpr, ob, act,
  Presheaf, FreePresheaf, coact,
  DisplayedCategory, Act, hom,
  MCategory, FreeMCategory, Tight, reflexive, transitive

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
compose(fs::AbstractVector) = foldl(compose, fs)
compose(f, g, h, fs...) = compose([f, g, h, fs...])

@syntax FreeCategory{ObExpr,HomExpr} Category begin
  compose(f::Hom, g::Hom) = associate_unit(new(f,g; strict=true), id)
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

function show(io::IO, ::MIME"text/plain", expr::HomExpr)
  show_unicode(io, expr)
  print(io, ": ")
  show_unicode(io, dom(expr))
  print(io, " → ")
  show_unicode(io, codom(expr))
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
  @op (⋅) := act

  # action equations
  act(act(x, f), g) == act(x, (f ⋅ g)) ⊣
    (A::Ob, B::Ob, C::Ob, f::(A → B), g::(B → C), x::El(A))
  act(x, id(A)) == x ⊣ (A::Ob, x::El(A))
end

abstract type ElExpr{T} <: GATExpr{T} end

@syntax FreeCopresheaf{ObExpr,HomExpr,ElExpr} Copresheaf begin
  compose(f::Hom, g::Hom) = associate_unit(new(f,g; strict=true), id)
end

""" Theory of *presheaves*.

Axiomatized as a contravariant category action.
"""
@theory Presheaf{Ob,Hom,El} <: Category{Ob,Hom} begin
  # presheaf = object-indexed family
  El(ob::Ob)::TYPE

  # functoriality = contravariant action
  coact(f::Hom(A,B), x::El(B))::El(A) ⊣ (A::Ob, B::Ob)
  @op (⋅) := coact

  # action equations
  coact(f, coact(g, x)) == coact((f ⋅ g), x) ⊣
    (A::Ob, B::Ob, C::Ob, f::(A → B), g::(B → C), x::El(C))
  coact(id(A), x) == x ⊣ (A::Ob, x::El(A))
end

@syntax FreePresheaf{ObExpr,HomExpr,ElExpr} Presheaf begin
  compose(f::Hom, g::Hom) = associate_unit(new(f,g; strict=true), id)
end

function show(io::IO, ::MIME"text/plain", expr::ElExpr)
  show_unicode(io, expr)
  print(io, ": ")
  show_unicode(io, ob(expr))
end
function show(io::IO, ::MIME"text/latex", expr::ElExpr)
  print(io, "\$")
  show_latex(io, expr)
  print(io, " : ")
  show_latex(io, ob(expr))
  print(io, "\$")
end

function show_unicode(io::IO, expr::Union{ElExpr{:act},ElExpr{:coact}}; kw...)
  Syntax.show_unicode_infix(io, expr, "⋅"; kw...)
end
function show_latex(io::IO, expr::Union{ElExpr{:act},ElExpr{:coact}};
                    paren::Bool=false, kw...)
  Syntax.show_latex_infix(io, expr, "\\cdot"; paren=paren)
end

# Displayed category
####################

""" Theory of a *displayed category*.

More precisely, this is the theory of a base category ``C`` (`Ob`,`Hom`) and a
displayed category (`El`,`Act`) over ``C``. Displayed categories axiomatize lax
functors ``C → **Span**`` or equivalently objects in ``**Cat**/C`` in a
pleasant, generalized algebraic style.

Reference: Ahrens & Lumsdaine 2019, "Displayed categories", Definition 3.1.
"""
@theory DisplayedCategory{Ob,Hom,El,Act} <: Category{Ob,Hom} begin
  El(ob::Ob)::TYPE
  Act(hom::Hom(A,B), dom::El(A), codom::El(B))::TYPE ⊣ (A::Ob, B::Ob)

  id(x::El(A))::Act(id(A),x,x) ⊣ (A::Ob)
  compose(f̄::Act(f,x,y), ḡ::Act(g,y,z))::Act(compose(f,g),x,z) ⊣
    (A::Ob, B::Ob, C::Ob, f::(A → B), g::(B → C))

  # Displayed category axioms: category axioms over the base category.
  ((f̄ ⋅ ḡ) ⋅ h̄ == f̄ ⋅ (ḡ ⋅ h̄) ⊣
    (A::Ob, B::Ob, C::Ob, D::Ob, f::(A → B), g::(B → C), h::(C → D),
     w::El(A), x::El(B), y::El(C), z::El(D),
     f̄::Act(f,w,x), ḡ::Act(g,x,y), h̄::Act(h,y,z)))
  f̄ ⋅ id(y) == f̄ ⊣ (A::Ob, B::Ob, f::(A → B), x::El(A), y::El(B), f̄::Act(f,x,y))
  id(x) ⋅ f̄ == f̄ ⊣ (A::Ob, B::Ob, f::(A → B), x::El(A), y::El(B), f̄::Act(f,x,y))
end

# ℳ-category
############

""" Theory of an *ℳ-category*.

The term "ℳ-category", used on the
[nLab](https://ncatlab.org/nlab/show/M-category) is not very common, but the
concept itself shows up commonly. An *ℳ-category* is a category with a
distinguished wide subcategory, whose morphisms are suggestively called *tight*;
for contrast, a generic morphism is called *loose*. Equivalently, an ℳ-category
is a category enriched in the category ℳ of injections, the full subcategory of
the arrow category of Set spanned by injections.

In the following GAT, tightness is axiomatized as a property of morphisms: a
dependent family of sets over the hom-sets, each having at most one inhabitant.
"""
@theory MCategory{Ob,Hom,Tight} <: Category{Ob,Hom} begin
  Tight(hom::Hom(A,B))::TYPE ⊣ (A::Ob, B::Ob)

  # Tightness is a property.
  t == t′ ⊣ (A::Ob, B::Ob, f::Hom(A,B), t::Tight(f), t′::Tight(f))

  # Tight morphisms form a subcategory.
  reflexive(A::Ob)::Tight(id(A))
  transitive(t::Tight(f), u::Tight(g))::Tight(compose(f,g)) ⊣
    (A::Ob, B::Ob, C::Ob, f::Hom(A,B), g::Hom(B,C), t::Tight(f), u::Tight(g))
end

abstract type TightExpr{T} <: GATExpr{T} end

@syntax FreeMCategory{ObExpr,HomExpr,TightExpr} MCategory begin
  compose(f::Hom, g::Hom) = associate_unit(new(f,g; strict=true), id)
  transitive(t::Tight, u::Tight) = associate_unit(new(t,u; strict=true), reflexive)
end
