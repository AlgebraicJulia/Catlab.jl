export CategoryWithProducts, ob, hom, terminal, product, proj1, proj2, pair,
  initial, coproduct, coproj1, coproj2, copair

# Limits
########

""" Theory of a *category with (finite) products*

Finite products are presented in biased style, via the nullary case (terminal
objects) and the binary case (binary products). The equational axioms are
standard, especially in type theory (Lambek & Scott, 1986, Section I.3).

For a monoidal category axiomatization, see [`CartesianCategory`](@ref).
"""
@theory Category(Ob,Hom) => CategoryWithProducts(Ob,Hom,Term,Prod) begin
  Term()::TYPE
  Prod(A::Ob, B::Ob)::TYPE
  
  terminal()::Term()
  product(A::Ob, B::Ob)::Prod(A,B)
  #@op (×) := product
  
  ob(⊤::Term())::Ob
  hom(⊤::Term(), C::Ob)::(C → ob(⊤))
  
  ob(Π::Prod(A,B))::Ob ⊣ (A::Ob, B::Ob)
  proj1(Π::Prod(A,B))::(ob(Π) → A) ⊣ (A::Ob, B::Ob)
  proj2(Π::Prod(A,B))::(ob(Π) → B) ⊣ (A::Ob, B::Ob)
  pair(Π::Prod(A,B), f::(C → A), g::(C → B))::(C → ob(Π)) ⊣ (A::Ob, B::Ob, C::Ob)
  
  # Projection axioms.
  (pair(Π,f,g) ⋅ proj1(Π) == f
    ⊣ (A::Ob, B::Ob, C::Ob, Π::Prod(A,B), f::(C → A), g::(C → B)))
  (pair(Π,f,g) ⋅ proj2(Π) == g
    ⊣ (A::Ob, B::Ob, C::Ob, Π::Prod(A,B), f::(C → A), g::(C → B)))
  
  # Uniqueness axioms.
  f == g ⊣ (C::Ob, ⊤::Term(), f::(C → ob(⊤)), g::(C → ob(⊤)))
  (pair(h⋅proj1(Π), h⋅proj2(Π)) == h
    ⊣ (A::Ob, B::Ob, C::Ob, Π::Prod(A,B), h::(C → ob(Π))))
end

# Colimits
##########

""" Theory of a *category with (finite) coproducts*

Finite coproducts are presented in biased style, via the nullary case (initial
objects) and the binary case (binary coproducts).

For a monoidal category axiomatization, see [`CocartesianCategory`](@ref).
"""
@theory Category(Ob,Hom) => CategoryWithCoproducts(Ob,Hom,Init,Coprod) begin
  Init()::TYPE
  Coprod(A::Ob, B::Ob)::TYPE
  
  initial()::Init()
  coproduct(A::Ob, B::Ob)::Coprod(A,B)
  #@op (⊔) := coproduct
  
  ob(⊥::Init())::Ob
  hom(⊥::Init(), C::Ob)::(ob(⊥) → C)
  
  ob(⨆::Coprod(A,B))::Ob ⊣ (A::Ob, B::Ob)
  coproj1(⨆::Coprod(A,B))::(A → ob(⨆)) ⊣ (A::Ob, B::Ob)
  coproj2(⨆::Coprod(A,B))::(B → ob(⨆)) ⊣ (A::Ob, B::Ob)
  copair(⨆::Coprod(A,B), f::(A → C), g::(B → C))::(ob(⨆) → C) ⊣ (A::Ob, B::Ob, C::Ob)
  
  # Coprojection axioms.
  (coproj1(⨆) ⋅ copair(⨆,f,g) == f
    ⊣ (A::Ob, B::Ob, C::Ob, ⨆::Coprod(A,B), f::(A → C), g::(B → C)))
  (coproj2(⨆) ⋅ copair(⨆,f,g) == g
    ⊣ (A::Ob, B::Ob, C::Ob, ⨆::Coprod(A,B), f::(A → C), g::(B → C)))
  
  # Uniqueness axioms.
  f == g ⊣ (C::Ob, ⊥::Init(), f::(ob(⊥) → C), g::(ob(⊥) → C))
  (copair(coproj1(⨆)⋅h, coproj2(⨆)⋅h) == h
    ⊣ (A::Ob, B::Ob, C::Ob, ⨆::Coprod(A,B), h::(ob(⨆) → C)))
end
