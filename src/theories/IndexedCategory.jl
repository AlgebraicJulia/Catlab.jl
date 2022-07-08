export DisplayedCategory, Fib, FibHom, ob, hom

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

  """ Fiber over a morphism, with given domain and codmain. """
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
