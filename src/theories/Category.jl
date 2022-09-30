export ThCategory, FreeCategory, Ob, Hom, dom, codom, id, compose, ⋅,
  ThGroupoid, FreeGroupoid, inv,
  ThCopresheaf, FreeCopresheaf, El, ElExpr, ob, act,
  ThPresheaf, FreePresheaf, coact,
  ThMCategory, FreeMCategory, Tight, reflexive, transitive

import Base: inv, show

# Category
##########

""" Theory of *categories*

**Note**: Throughout Catlab, we compose morphisms in diagrammatic order (from
left to right), i.e., if ``f:A→B`` and ``g:B→C`` then the composite morphism
``f⋅g:A→C`` is `compose(f,g)`. Under this convention, functions are applied on
the right, e.g., if ``a ∈ A`` then ``af ∈ B``.

We retain the usual meaning of the symbol ``∘`` (`\\circ`), i.e., ``g∘f`` is
`compose(f,g)`. This usage is too entrenched to overturn. However, we use the
symbol ``⋅`` (`\\cdot`) for composition in diagrammatic order.
"""
@theory ThCategory{Ob,Hom} begin
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

@syntax FreeCategory{ObExpr,HomExpr} ThCategory begin
  compose(f::Hom, g::Hom) = associate_unit(new(f,g; strict=true), id)
end

show_unicode(io::IO, expr::CategoryExpr{:compose}; kw...) =
  Syntax.show_unicode_infix(io, expr, "⋅"; kw...)

show_latex(io::IO, expr::CategoryExpr{:id}; kw...) =
  Syntax.show_latex_script(io, expr, "\\mathrm{id}")
show_latex(io::IO, expr::CategoryExpr{:compose}; paren::Bool=false, kw...) =
  Syntax.show_latex_infix(io, expr, "\\cdot"; paren=paren)

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

# Groupoid
##########

""" Theory of *groupoids*.
"""
@theory ThGroupoid{Ob,Hom} <: ThCategory{Ob,Hom} begin
  inv(f::(A → B))::(B → A) ⊣ (A::Ob, B::Ob)

  f ⋅ inv(f) == id(A) ⊣ (A::Ob, B::Ob, f::(A → B))
  inv(f) ⋅ f == id(B) ⊣ (A::Ob, B::Ob, f::(A → B))
end

@syntax FreeGroupoid{ObExpr,HomExpr} ThGroupoid begin
  compose(f::Hom, g::Hom) = associate_unit_inv(new(f,g; strict=true), id, inv)
  inv(f::Hom) = distribute_unary(involute(new(f)), inv, compose,
                                 unit=id, contravariant=true)
end

# (Co)presheaf
##############

""" Theory of *copresheaves*.

Axiomatized as a covariant category action.
"""
@theory ThCopresheaf{Ob,Hom,El} <: ThCategory{Ob,Hom} begin
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

@syntax FreeCopresheaf{ObExpr,HomExpr,ElExpr} ThCopresheaf begin
  compose(f::Hom, g::Hom) = associate_unit(new(f,g; strict=true), id)
end

""" Theory of *presheaves*.

Axiomatized as a contravariant category action.
"""
@theory ThPresheaf{Ob,Hom,El} <: ThCategory{Ob,Hom} begin
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

@syntax FreePresheaf{ObExpr,HomExpr,ElExpr} ThPresheaf begin
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

show_unicode(io::IO, expr::Union{ElExpr{:act},ElExpr{:coact}}; kw...) =
  Syntax.show_unicode_infix(io, expr, "⋅"; kw...)

show_latex(io::IO, expr::Union{ElExpr{:act},ElExpr{:coact}};
           paren::Bool=false, kw...) =
  Syntax.show_latex_infix(io, expr, "\\cdot"; paren=paren)

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
@theory ThMCategory{Ob,Hom,Tight} <: ThCategory{Ob,Hom} begin
  Tight(hom::Hom(A,B))::TYPE ⊣ (A::Ob, B::Ob)

  # Tightness is a property.
  t == t′ ⊣ (A::Ob, B::Ob, f::Hom(A,B), t::Tight(f), t′::Tight(f))

  # Tight morphisms form a subcategory.
  reflexive(A::Ob)::Tight(id(A))
  transitive(t::Tight(f), u::Tight(g))::Tight(compose(f,g)) ⊣
    (A::Ob, B::Ob, C::Ob, f::Hom(A,B), g::Hom(B,C), t::Tight(f), u::Tight(g))
end

abstract type TightExpr{T} <: GATExpr{T} end

@syntax FreeMCategory{ObExpr,HomExpr,TightExpr} ThMCategory begin
  compose(f::Hom, g::Hom) = associate_unit(new(f,g; strict=true), id)
  transitive(t::Tight, u::Tight) = associate_unit(new(t,u; strict=true), reflexive)
end
