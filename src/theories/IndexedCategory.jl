export DisplayedCategory, Fib, FibHom, ob, hom,
  IndexedCategory, act, ⊙

# Displayed category
####################

""" Theory of a *displayed category*.

More precisely, this is the theory of a category ``C`` (`Ob`,`Hom`) together
with a displayed category over ``C`` (`Fib`,`FibHom`). Displayed categories
axiomatize lax functors ``C → **Span**``, or equivalently objects of a slice
category ``**Cat**/C``, in a generalized algebraic style.

Reference: Ahrens & Lumsdaine 2019, "Displayed categories", Definition 3.1.
"""
@theory DisplayedCategory{Ob,Hom,Fib,FibHom} <: Category{Ob,Hom} begin
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

# Indexed category
##################

""" Theory of a (covariantly) *indexed category*.

An *indexed category* is a **Cat**-valued pseudofunctor. For simplicitly, we
assume that the functor is strict.

Just as a copresheaf, or **Set**-valued functor, can be seen as a category
action of a family of sets, an indexed category can be seen as a category action
on a family of categories. This picture guides our axiomatization of an indexed
category as a generalized algebraic theory.
"""
@theory IndexedCategory{Ob,Hom,Fib,FibHom} <: Category{Ob,Hom} begin
  @op begin
    (→) := FibHom
    (⊙) := act
  end

  Fib(ob::Ob)::TYPE
  FibHom(dom::Fib(A), codom::Fib(A))::TYPE ⊣ (A::Ob)

  id(X::Fib(A))::FibHom(X,X) ⊣ (A::Ob)
  compose(u::FibHom(X,Y), v::FibHom(Y,Z))::FibHom(X,Z) ⊣
    (A::Ob, X::Fib(A), Y::Fib(A), Z::Fib(A))

  # Category axioms for each fiber.
  ((u ⋅ v) ⋅ w == u ⋅ (v ⋅ w)
   ⊣ (A::Ob, W::Fib(A), X::Fib(A), Y::Fib(A), Z::Fib(A),
      u::(W → X), v::(X → Y), w::(Y → Z)))
  u ⋅ id(X) == u ⊣ (A::Ob, X::Fib(A), Y::Fib(A), u::(X → Y))
  id(X) ⋅ u == u ⊣ (A::Ob, X::Fib(A), Y::Fib(A), v::(X → Y))

  # Transitions between fibers.
  act(X::Fib(A), f::(A → B))::Fib(B) ⊣ (A::Ob, B::Ob)
  act(u::(X → Y), f::(A → B))::(act(X,f) → act(Y,f)) ⊣
    (A::Ob, B::Ob, X::Fib(A), Y::Fib(A))

  # Functorality of transitions.
  (u⋅v)⊙f == (u⊙f) ⋅ (v⊙f) ⊣ (A::Ob, B::Ob, X::Fib(A), Y::Fib(A), Z::Fib(A),
                              f::(A → B), u::(X → Y), v::(Y → Z))
  (id(X))⊙f == id(X⊙f) ⊣ (A::Ob, B::Ob, X::Fib(A), f::(A → B))

  X⊙(f⋅g) == (X⊙f)⊙g ⊣ (A::Ob, B::Ob, C::Ob, X::Fib(A), f::(A → B), g::(A → C))
  u⊙(f⋅g) == (u⊙f)⊙g ⊣ (A::Ob, B::Ob, C::Ob, X::Fib(A), Y::Fib(A),
                        f::(A → B), g::(B → C), u::(X → Y))
  X⊙(id(A)) == X ⊣ (A::Ob, X::Fib(A))
  u⊙(id(A)) == u ⊣ (A::Ob, X::Fib(A), Y::Fib(A), u::(X → Y))
end
