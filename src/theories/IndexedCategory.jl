export DisplayedCategory, El, Act, ob, hom

# Displayed category
####################

""" Theory of a *displayed category*.

More precisely, this is the theory of a base category ``C`` (`Ob`,`Hom`) and a
displayed category (`El`,`Act`) over ``C``. Displayed categories axiomatize lax
functors ``C → **Span**``, or equivalently objects of a slice category
``**Cat**/C``, in a generalized algebraic style.

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
