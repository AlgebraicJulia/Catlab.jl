export ThDisplayedCategory, Fib, FibHom, ob, hom,
  ThOpindexedCategory, act,
  ThOpindexedMonoidalCategory, ThOpindexedMonoidalCategoryLax

import Base: *

# Displayed category
####################

""" Theory of a *displayed category*.

More precisely, this is the theory of a category ``C`` (`Ob`,`Hom`) together
with a displayed category over ``C`` (`Fib`,`FibHom`). Displayed categories
axiomatize lax functors ``C → **Span**``, or equivalently objects of a slice
category ``**Cat**/C``, in a generalized algebraic style.

References:

- [nLab: displayed category](https://ncatlab.org/nlab/show/displayed+category)
- Ahrens & Lumsdaine, 2019: Displayed categories, Definition 3.1
"""
@theory ThDisplayedCategory{Ob,Hom,Fib,FibHom} <: ThCategory{Ob,Hom} begin
  """ Fiber over an object. """
  Fib(ob::Ob)::TYPE

  """ Fiber over a morphism, with given fibers over the domain and codomain. """
  FibHom(hom::Hom(A,B), dom::Fib(A), codom::Fib(B))::TYPE ⊣ (A::Ob, B::Ob)

  id(x::Fib(A))::FibHom(id(A),x,x) ⊣ (A::Ob)
  compose(f̄::FibHom(f,x,y), ḡ::FibHom(g,y,z))::FibHom(compose(f,g),x,z) ⊣
    (A::Ob, B::Ob, C::Ob, f::(A → B), g::(B → C))

  # Displayed category axioms: category axioms over the base category.
  ((f̄ ⋅ ḡ) ⋅ h̄ == f̄ ⋅ (ḡ ⋅ h̄) ⊣
    (A::Ob, B::Ob, C::Ob, D::Ob, f::(A → B), g::(B → C), h::(C → D),
     w::Fib(A), x::Fib(B), y::Fib(C), z::Fib(D),
     f̄::FibHom(f,w,x), ḡ::FibHom(g,x,y), h̄::FibHom(h,y,z)))
  f̄ ⋅ id(y) == f̄ ⊣ (A::Ob, B::Ob, f::(A → B),
                    x::Fib(A), y::Fib(B), f̄::FibHom(f,x,y))
  id(x) ⋅ f̄ == f̄ ⊣ (A::Ob, B::Ob, f::(A → B),
                    x::Fib(A), y::Fib(B), f̄::FibHom(f,x,y))
end

# Opindexed category
####################

""" Theory of an opindexed, or covariantly indexed, category.

An *opindexed category* is a **Cat**-valued pseudofunctor. For simplicitly, we
assume that the functor is strict.

Just as a copresheaf, or **Set**-valued functor, can be seen as a category
action on a family of sets, an opindexed category can be seen as a category
action on a family of categories. This picture guides our axiomatization of an
opindexed category as a generalized algebraic theory. The symbol `*` is used for
the actions since a common mathematical notation for the "pushforward functor"
induced by an indexing morphism ``f: A → B`` is ``f_*: F(A) \to F(B)``.
"""
@theory ThOpindexedCategory{Ob,Hom,Fib,FibHom} <: ThCategory{Ob,Hom} begin
  @op begin
    (→) := FibHom
    (*) := act
  end

  Fib(ob::Ob)::TYPE
  FibHom(dom::Fib(A), codom::Fib(A))::TYPE ⊣ (A::Ob)

  # Category operations for each fiber.
  id(X::Fib(A))::FibHom(X,X) ⊣ (A::Ob)
  compose(u::FibHom(X,Y), v::FibHom(Y,Z))::FibHom(X,Z) ⊣
    (A::Ob, X::Fib(A), Y::Fib(A), Z::Fib(A))

  # Transitions between fibers.
  act(X::Fib(A), f::(A → B))::Fib(B) ⊣ (A::Ob, B::Ob)
  act(u::(X → Y), f::(A → B))::(act(X,f) → act(Y,f)) ⊣
    (A::Ob, B::Ob, X::Fib(A), Y::Fib(A))

  # Category axioms for each fiber.
  ((u ⋅ v) ⋅ w == u ⋅ (v ⋅ w)
   ⊣ (A::Ob, W::Fib(A), X::Fib(A), Y::Fib(A), Z::Fib(A),
      u::(W → X), v::(X → Y), w::(Y → Z)))
  u ⋅ id(X) == u ⊣ (A::Ob, X::Fib(A), Y::Fib(A), u::(X → Y))
  id(X) ⋅ u == u ⊣ (A::Ob, X::Fib(A), Y::Fib(A), v::(X → Y))

  # Functorality of transitions.
  (u⋅v)*f == (u*f)⋅(v*f) ⊣ (A::Ob, B::Ob, X::Fib(A), Y::Fib(A), Z::Fib(A),
                            f::(A → B), u::(X → Y), v::(Y → Z))
  (id(X))*f == id(X*f) ⊣ (A::Ob, B::Ob, X::Fib(A), f::(A → B))

  X*(f⋅g) == (X*f)*g ⊣ (A::Ob, B::Ob, C::Ob, X::Fib(A), f::(A → B), g::(A → C))
  u*(f⋅g) == (u*f)*g ⊣ (A::Ob, B::Ob, C::Ob, X::Fib(A), Y::Fib(A),
                        f::(A → B), g::(B → C), u::(X → Y))
  X*(id(A)) == X ⊣ (A::Ob, X::Fib(A))
  u*(id(A)) == u ⊣ (A::Ob, X::Fib(A), Y::Fib(A), u::(X → Y))
end

# Opindexed monoidal category
#############################

# Not a standard or appealing theory, but a building block for those below.
@theory ThOpindexedMonoidalCategoryPre{Ob,Hom,Fib,FibHom} <: ThOpindexedCategory{Ob,Hom,Fib,FibHom} begin
  @op (⊗) := otimes

  # Monoid operations in each fiber.
  otimes(X::Fib(A), Y::Fib(A))::Fib(A) ⊣ (A::Ob)
  otimes(u::(X → Y), v::(W → Z))::(otimes(X,W) → otimes(Y,Z)) ⊣
    (A::Ob, W::Fib(A), X::Fib(A), Y::Fib(A), Z::Fib(A))
  munit(A::Ob)::Fib(A)

  # Monoid axioms for each fiber.
  (X ⊗ Y) ⊗ Z == X ⊗ (Y ⊗ Z) ⊣ (A::Ob, X::Fib(A), Y::Fib(A), Z::Fib(A))
  munit(A) ⊗ X == X ⊣ (A::Ob, X::Fib(A))
  X ⊗ munit(A) == X ⊣ (A::Ob, X::Fib(A))
  ((u ⊗ v) ⊗ w == u ⊗ (v ⊗ w) ⊣
    (A::Ob, U::Fib(A), V::Fib(A), W::Fib(A), X::Fib(A), Y::Fib(A), Z::Fib(A),
     u::(U → X), v::(V → Y), w::(W → Z)))
  id(munit(A)) ⊗ u == u ⊣ (A::Ob, X::Fib(A), Y::Fib(A), u::(X → Y))
  u ⊗ id(munit(A)) == u ⊣ (A::Ob, X::Fib(A), Y::Fib(A), u::(X → Y))

  # Monoid functorality axioms for each fiber.
  ((t ⊗ u) ⋅ (v ⊗ w) == (t ⋅ v) ⊗ (u ⋅ w)
    ⊣ (A::Ob, U::Fib(A), V::Fib(A), W::Fib(A), X::Fib(A), Y::Fib(A), Z::Fib(A),
       t::(U → V), v::(V → W), u::(X → Y), w::(Y → Z)))
  id(X ⊗ Y) == id(X) ⊗ id(Y) ⊣ (A::Ob, X::Fib(A), Y::Fib(A))
end

""" Theory of an opindexed, or covariantly indexed, monoidal category.

An *opindexed monoidal category* is a pseudofunctor into **MonCat**, the
2-category of monoidal categories, strong monoidal functors, and monoidal
natural transformations. For simplicity, we take the pseudofunctor, the monoidal
categories, and the monoidal functors all to be strict.

References:

- [nLab: indexed monoidal category](https://ncatlab.org/nlab/show/indexed+monoidal+category)
- Shulman, 2008: Framed bicategories and monoidal fibrations
- Shulman, 2013: Enriched indexed categories
"""
@theory ThOpindexedMonoidalCategory{Ob,Hom,Fib,FibHom} <: ThOpindexedMonoidalCategoryPre{Ob,Hom,Fib,FibHom} begin
  (X ⊗ Y) * f == (X*f) ⊗ (Y*f) ⊣ (A::Ob, B::Ob, X::Fib(A), Y::Fib(A), f::(A → B))
  munit(A) * f == munit(B) ⊣ (A::Ob, B::Ob, f::(A → B))

  (u ⊗ v) * f == (u*f) ⊗ (v*f) ⊣
    (A::Ob, B::Ob, X::Fib(A), Y::Fib(A), Z::Fib(A), W::Fib(A),
     f::(A → B), u::(X → Z), v::(Y → W))
end

""" Theory of an opindexed monoidal category with lax transition functors.

This is a pseudofunctor into **MonCatLax**, the 2-category of monoidal
categories, *lax* monoidal functors, and monoidal natural transformations. In
(Hofstra & De Marchi 2006), these are called simply "(op)indexed monoidal
categories," but that is not the standard usage.

References:

- Hofstra & De Marchi, 2006: Descent for monads
- Moeller & Vasilakopoulou, 2020: Monoidal Grothendieck construction, Remark
  3.18 [this paper is about monoidal indexed categories, a different notion!]
"""
@theory ThOpindexedMonoidalCategoryLax{Ob,Hom,Fib,FibHom} <: ThOpindexedMonoidalCategoryPre{Ob,Hom,Fib,FibHom} begin
  # Components of the laxator for `f: A → B`.
  otimes(f::(A → B), X::Fib(A), Y::Fib(A))::(((X*f) ⊗ (Y*f)) → ((X⊗Y) * f)) ⊣
    (A::Ob, B::Ob)
  munit(f::(A → B))::(munit(B) → (munit(A)*f)) ⊣ (A::Ob, B::Ob)

  # Naturality for laxity cells.
  ⊗(f,X,Y) ⋅ ((u⊗v) * f) == ((u*f) ⊗ (v*f)) ⋅ ⊗(f,Z,W) ⊣
    (A::Ob, B::Ob, X::Fib(A), Y::Fib(A), Z::Fib(A), W::Fib(A),
     f::(A → B), u::(X → Z), v::(Y → W))

  # Functorality of laxity cells.
  ⊗(f⋅g,X,Y) == ⊗(g,X*f,Y*f) ⋅ (⊗(f,X,Y)*g) ⊣
    (A::Ob, B::Ob, C::Ob, f::(A → B), g::(B → C), X::Fib(A), Y::Fib(A))
  ⊗(id(A),X,Y) == id(X⊗Y) ⊣ (A::Ob, X::Fib(A), Y::Fib(A))
end
